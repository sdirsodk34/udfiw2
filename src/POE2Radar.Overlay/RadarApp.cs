using System.Linq;
using System.Runtime.InteropServices;
using NumVec2 = System.Numerics.Vector2;
using POE2Radar.Core;
using POE2Radar.Core.Game;
using POE2Radar.Overlay.Config;
using POE2Radar.Overlay.Native;
using POE2Radar.Overlay.Navigation;
using POE2Radar.Overlay.Web;

namespace POE2Radar.Overlay;

/// <summary>
/// Drives the PoE2 radar: per-tick resolve chain → read player/entities/terrain/map → render.
/// Read-only. Render rate is configurable (RadarSettings.FpsCap, default 60 Hz).
/// </summary>
public sealed class RadarApp : IDisposable
{
    private const int WorldHz = 30;

    private readonly ProcessHandle _process;
    private readonly MemoryReader _reader;
    private readonly Poe2Live _live;
    private readonly Poe2Atlas _atlas;
    private readonly OverlayWindow _window;
    private readonly OverlayRenderer _renderer;
    private readonly ApiServer _api;
    private readonly RadarSettings _settings;
    private readonly HiddenEntities _hidden;
    private readonly WatchedEntities _watched;
    private readonly LandmarkPatterns _landmarkPatterns;
    private readonly DisplayRules _displayRules;
    private Func<Poe2Live.EntityDot, DisplayRule?>? _resolveEntity;
    private Func<string, DisplayRule?>? _resolveTileDraw;
    private readonly LandmarkStore _landmarkStore;
    private int _landmarkGen;
    private int _displayRulesGen;
    private int _landmarkStoreGen;
    private int _appliedClusterGap;
    private nint _areaInstanceForApi;   
    private nint _inGameStateForApi;    
    private volatile RadarState _state = RadarState.Empty;

    // ── Atlas overlay state ──
    private readonly object _atlasLock = new();
    private readonly HashSet<nint> _atlasSel = new();   
    private bool _atlasOpen;
    private List<AtlasMark> _atlasMarks = new();         
    private DateTime _nextInspectAt = DateTime.MinValue; 
    private (int X, int Y)? _atlasStartGrid;
    private (int X, int Y)? _atlasGoalGrid;
    private NumVec2? _atlasStartPt, _atlasEndPt; 
    private List<NumVec2> _atlasRoute = new();   
    private DateTime _atlasGoodAt = DateTime.MinValue; 
    private long _lastAtlasSig;          
    private bool _builtAtlasOnce;        
    private volatile float _atlasZoom = 0.85f;
    private volatile UpdateChecker.Result? _update;   

    private static string ConfigDir => Path.Combine(AppContext.BaseDirectory, "config");

    private DateTime _worldAt = DateTime.MinValue;
    private List<Poe2Live.EntityDot> _entities = new();
    private readonly record struct HpBarSpec(nint Entity, float Width, uint Fill, float BorderWidth, uint Border);
    private readonly List<HpBarSpec> _hpSpecs = new();
    private readonly List<HpBarTarget> _hpFrame = new();
    private IReadOnlyList<Poe2Live.Landmark> _landmarks = Array.Empty<Poe2Live.Landmark>();
    private Poe2Live.TerrainData? _terrain;
    private uint _areaHash;
    private nint _lastAreaInstance;
    private nint _gameHwnd;
    private volatile bool _shutdown;

    // ── Auto-flask System Disabled ──
    private readonly bool _autoFlask = false; 
    private DateTime _nextPathKeyAt = DateTime.MinValue;
    private DateTime _nextBrowserAt = DateTime.MinValue;
    private float _hpPct = 100f, _manaPct = 100f, _esPct = 100f;
    private string _flaskNote = "DISABLED";
    private string _areaCode = "", _charName = "";
    private nint _charNameFor;   
    private int _charLevel;
    private float[]? _cameraMatrix;

    private List<string> _selectedSnapshot = new();
    private IReadOnlyList<LegendEntry> _legend = Array.Empty<LegendEntry>();
    private bool _overlayHadContent;

    private const int AddNearestVk = 0x75; // F6
    private const int ClearPathsVk = 0x76; // F7
    private const int MaxSelectedTargets = 8; 
    private readonly BackgroundReplanner _replanner = new();
    private readonly Dictionary<string, RouteTracker> _trackers = new(); 
    private List<NavTarget> _navTargets = new();                                         
    private readonly object _navLock = new();
    private readonly List<string> _selectedIds = new();                                  
    private List<SelectedPath> _selectedPaths = new();                                   
    private nint _navTargetsArea = -1;                                                   
    private readonly Dictionary<uint, List<string>> _zoneSelections = new();
    private readonly List<uint> _zoneOrder = new();                                      
    private uint _selectionAreaHash;
    private const int MaxRememberedZones = 64;

    private bool _navMenuExpanded;                                                       

    public void RequestShutdown() => _shutdown = true;

    public RadarApp(ProcessHandle process, MemoryReader reader, nint gameStateSlot)
    {
        _process = process;
        _reader = reader;
        _settings = RadarSettings.Load();
        Console.WriteLine($"Settings: {RadarSettings.FilePath}");
        Console.WriteLine($"Entity names: {EntityNameResolver.Shared.Count} mappings; zones: {ZoneGuide.Shared.Count}");
        _live = new Poe2Live(reader, gameStateSlot);
        _atlas = new Poe2Atlas(reader);
        _window = OverlayWindow.Create();
        _renderer = new OverlayRenderer(_window);
        _window.OnClientClick = OnOverlayClick;
        _hidden = new HiddenEntities(Path.Combine(ConfigDir, "hidden_entities.json"));
        _watched = new WatchedEntities(Path.Combine(ConfigDir, "watched_entities.json"));
        _landmarkPatterns = new LandmarkPatterns(Path.Combine(ConfigDir, "landmark_patterns.json"));
        _live.CustomLandmarkMatch = TileLandmarkMatch; 
        _landmarkGen = _landmarkPatterns.Generation;
        _live.LandmarkClusterGap = _settings.LandmarkClusterGap;
        _appliedClusterGap = _settings.LandmarkClusterGap;
        
        _displayRules = new DisplayRules(Path.Combine(ConfigDir, "display_rules.json"));
        _resolveEntity = _displayRules.Resolve;
        _resolveTileDraw = p => _displayRules.ResolveTile(p, requireMatch: false);
        if (_displayRules.Count == 0)
        {
            _displayRules.Replace(DisplayRules.BuildDefault(
                _settings.Styles, _settings.ShowMonsters, _watched.All));
            Console.WriteLine($"Display rules: seeded {_displayRules.Count} from legacy config (first run).");
        }
        
        if (_landmarkPatterns.All.Count > 0)
        {
            var rules = _displayRules.All.ToList();
            var seen = new HashSet<string>(
                rules.Where(r => r.Categories.Contains("Tile")).SelectMany(r => r.Match), StringComparer.OrdinalIgnoreCase);
            var added = 0;
            foreach (var lp in _landmarkPatterns.All)
            {
                if (!seen.Add(lp.Pattern)) continue;
                rules.Add(new DisplayRule
                {
                    Enabled = lp.Enabled, Name = string.IsNullOrWhiteSpace(lp.Label) ? lp.Pattern : lp.Label,
                    Categories = new() { "Tile" }, Match = new() { lp.Pattern },
                    Shape = "Diamond", Color = "#F259F2", Opacity = 1f, Size = 5f, Navigable = true,
                    Label = string.IsNullOrWhiteSpace(lp.Label) ? null : lp.Label,
                });
                added++;
            }
            if (added > 0) _displayRules.Replace(rules);
            foreach (var lp in _landmarkPatterns.All.ToList()) _landmarkPatterns.Remove(lp.Pattern);
            Console.WriteLine($"Migrated {added} landmark-tile pattern(s) into Tile display rules.");
        }
        
        if (_settings.AutoNavPatterns.Count > 0)
        {
            var rules = _displayRules.All.ToList();
            var pats = _settings.AutoNavPatterns;
            var changed = false;
            foreach (var r in rules)
            {
                if (r.Navigable) continue;
                if (r.Match.Any(m => pats.Any(p =>
                        m.Contains(p, StringComparison.OrdinalIgnoreCase) || p.Contains(m, StringComparison.OrdinalIgnoreCase))))
                { r.Navigable = true; changed = true; }
            }
            if (changed) _displayRules.Replace(rules);
            _settings.AutoNavPatterns = new(); _settings.Save();
            Console.WriteLine("Migrated auto-path patterns onto display rules' Auto-path flag.");
        }
        _displayRulesGen = _displayRules.Generation;
        _landmarkStore = new LandmarkStore(Path.Combine(ConfigDir, "landmarks.json"));
        _live.CuratedLookup = _landmarkStore.Lookup;
        _landmarkStoreGen = _landmarkStore.Generation;
        Console.WriteLine($"Hidden entities: {_hidden.Count} pattern(s); display rules: {_displayRules.Count}");
        
        _api = new ApiServer(() => _state, _settings, GetNavSelection, ToggleNavTarget, ClearNavSelection,
                             _hidden, _displayRules, _landmarkStore, CurrentTilePaths, AtlasJson, SetAtlasSelection,
                             SetAtlasHighlight, VersionJson, _settings.ApiPort);
        try { _api.Start(); Console.WriteLine($"API on http://localhost:{_settings.ApiPort} (dashboard at /)"); }
        catch (Exception ex) { Console.Error.WriteLine($"API server disabled: {ex.Message}"); }
        Console.WriteLine("Hotkeys: F6=add nearest path target  F7=clear path targets  "
                          + "F9=quit  F12=open dashboard");
        
        _ = Task.Run(async () =>
        {
            var u = await UpdateChecker.CheckAsync();
            _update = u;
            if (u.UpdateAvailable)
                Console.WriteLine($"\n*** UPDATE AVAILABLE: {u.Latest} — you have v{u.Current}. Download: {u.Url} ***\n");
            else
                Console.WriteLine($"POE2Radar v{u.Current}" + (u.Latest != null ? " (up to date)." : " (update check unavailable)."));
        });
    }

    private object VersionJson()
    {
        var u = _update;
        return new
        {
            current = u?.Current ?? UpdateChecker.Current,
            latest = u?.Latest,
            updateAvailable = u?.UpdateAvailable ?? false,
            url = u?.Url ?? UpdateChecker.ReleasesPage,
        };
    }

    public void Run()
    {
        _gameHwnd = OverlayNative.FindWindowForProcess(_process.ProcessId);
        while (!_shutdown)
        {
            if (_gameHwnd == 0) _gameHwnd = OverlayNative.FindWindowForProcess(_process.ProcessId);
            if (_gameHwnd != 0) _window.TrackGameWindow(_gameHwnd);
            if (!_window.PumpMessages()) break;
            Tick();
            var hz = Math.Clamp(_settings.FpsCap, 15, 360);
            Thread.Sleep(Math.Max(1, 1000 / hz));
        }
    }

    private void Tick()
    {
        HandleHotkeys();

        var inGame = _live.TryResolve(out var inGameState, out var areaInstance, out var localPlayer);
        var player = NumVec2.Zero;
        var map = default(Poe2Live.MapUi);
        var areaLevel = 0;

        if (inGame)
        {
            if (areaInstance != _lastAreaInstance) { _terrain = null; _lastAreaInstance = areaInstance; }
            _areaInstanceForApi = areaInstance; 
            _inGameStateForApi = inGameState;   
            _areaHash = _live.AreaHash(areaInstance);
            areaLevel = _live.AreaLevel(areaInstance);

            player = _live.PlayerGrid(localPlayer) ?? NumVec2.Zero;
            map = _live.ReadMap(inGameState, areaInstance);
            _areaCode = _live.AreaCode(areaInstance);
            if (localPlayer != _charNameFor) { _charNameFor = localPlayer; _charName = _live.PlayerName(localPlayer); }
            _cameraMatrix = _live.CameraMatrix(inGameState);

            if (_live.PlayerVitals(localPlayer) is { } v)
            {
                _hpPct = v.HpPct; _manaPct = v.ManaPct; _esPct = v.EsPct;
            }

            var now = DateTime.UtcNow;
            if ((now - _worldAt).TotalMilliseconds >= 1000.0 / WorldHz)
            {
                _worldAt = now;
                _charLevel = _live.PlayerLevel(localPlayer);   
                _terrain ??= _live.Terrain(areaInstance);
                _entities = _live.Entities(areaInstance);
                if (localPlayer != 0)
                    _entities = _entities.Where(e => e.Address != localPlayer).ToList();
                if (_hidden.Count > 0)
                    _entities = _entities.Where(e => !_hidden.IsHidden(e.Metadata)).ToList();
                if (_landmarkPatterns.Generation != _landmarkGen)
                {
                    _landmarkGen = _landmarkPatterns.Generation;
                    _live.InvalidateLandmarks();
                }
                if (_displayRules.Generation != _displayRulesGen)
                {
                    _displayRulesGen = _displayRules.Generation;
                    _live.InvalidateLandmarks();
                }
                if (_landmarkStore.Generation != _landmarkStoreGen)
                {
                    _landmarkStoreGen = _landmarkStore.Generation;
                    _live.InvalidateLandmarks();
                }
                if (_settings.LandmarkClusterGap != _appliedClusterGap)
                {
                    _appliedClusterGap = _settings.LandmarkClusterGap;
                    _live.LandmarkClusterGap = _appliedClusterGap;
                    _live.InvalidateLandmarks();
                }
                _landmarks = _live.Landmarks(areaInstance); 

                BuildHpSpecs();
                UpdateAtlas(inGameState);
                _navTargets = BuildNavTargets(player);

                if (areaInstance != _navTargetsArea)
                {
                    _navTargetsArea = areaInstance;
                    OnAreaChanged();
                }

                PruneCompletedTargets();
                MaintainRoutes(player);

                _selectedSnapshot = SnapshotSelection();
                _legend = BuildLegend(_selectedSnapshot);
            }

            _hpFrame.Clear();
            foreach (var spec in _hpSpecs)
            {
                if (!_live.TryLiveBar(spec.Entity, out var w, out var cur, out var max) || max <= 0 || cur <= 0) continue;
                _hpFrame.Add(new HpBarTarget(w, Math.Clamp((float)cur / max, 0f, 1f), spec.Width, spec.Fill, spec.BorderWidth, spec.Border));
            }
        }
        else
        {
            _selectedPaths = new List<SelectedPath>();
            _atlasOpen = false;
            if (_hpFrame.Count > 0) _hpFrame.Clear();
            if (_hpSpecs.Count > 0) _hpSpecs.Clear();
        }

        _state = new RadarState(inGame, _areaHash, areaLevel, map.IsVisible, map.Zoom, player, _entities, _landmarks,
            _hpPct, _manaPct, _esPct, _autoFlask, _flaskNote, _areaCode, _charName, _charLevel);

        var realActive = _gameHwnd != 0 && GetForegroundWindow() == _gameHwnd;
        var drawActive = realActive || _settings.AlwaysShowOverlay;
        var atlasProj = AtlasProjection(); 
        var ctx = new RenderContext(
            InGame: inGame,
            Active: drawActive,
            WindowWidth: _window.Width,
            WindowHeight: _window.Height,
            PlayerGrid: player,
            Map: map,
            Entities: _entities,
            Landmarks: _landmarks,
            AreaHash: _areaHash,
            Terrain: _terrain,
            ScaleMul: _settings.ScaleMul,
            OffsetX: _settings.OffX,
            OffsetY: _settings.OffY,
            HpPct: _hpPct,
            ManaPct: _manaPct,
            EsPct: _esPct,
            FlaskNote: _flaskNote,
            AreaCode: _areaCode,
            CharLevel: _charLevel,
            CameraMatrix: _cameraMatrix,
            HideJunk: _settings.HideJunk,
            ShowPath: _settings.ShowPath,
            UseCuratedLandmarks: _settings.UseCuratedLandmarks,
            ShowMonsters: _settings.ShowMonsters,
            ShowTerrain: _settings.ShowTerrain,
            ShowPlayerBlip: _settings.ShowPlayerBlip,
            HpBarNormal: _settings.HpBarNormal,
            HpBarMagic: _settings.HpBarMagic,
            HpBarRare: _settings.HpBarRare,
            HpBarUnique: _settings.HpBarUnique,
            SelectedPaths: _selectedPaths,
            IsSelected: _selectedSnapshot.Contains,
            Legend: _legend,
            NavMenuExpanded: _navMenuExpanded,
            NavMenuCorner: _settings.NavMenuCorner,
            Styles: _settings.Styles,
            HpBars: _settings.HpBars,
            HpBarTargets: _hpFrame,
            TerrainStyle: _settings.Terrain,
            Resolve: _resolveEntity,
            ResolveTile: _resolveTileDraw,
            AtlasOpen: _atlasOpen,
            AtlasNodes: _atlasMarks,
            AtlasScale: (float)atlasProj[0],
            AtlasScaleY: (float)atlasProj[4],
            AtlasOffX: (float)atlasProj[2],
            AtlasOffY: (float)atlasProj[5],
            AtlasShearX: (float)atlasProj[1],
            AtlasShearY: (float)atlasProj[3],
            AtlasPersX: (float)atlasProj[6],
            AtlasPersY: (float)atlasProj[7],
            AtlasStart: (_atlasOpen && _settings.AtlasShowRoute) ? _atlasStartPt : null,
            AtlasEnd: (_atlasOpen && _settings.AtlasShowRoute) ? _atlasEndPt : null,
            AtlasRoute: (_atlasOpen && _settings.AtlasShowRoute && _atlasRoute.Count >= 2) ? _atlasRoute : null);

        if (ctx.Active || _overlayHadContent)
        {
            _renderer.Render(ctx);
            _overlayHadContent = ctx.Active;
        }

        UpdateClickThrough(realActive);
    }

    private void UpdateClickThrough(bool active)
    {
        var overWidget = active
                         && _renderer.LegendRowRects.Count > 0
                         && OverlayNative.GetCursorPos(out var pt)
                         && HitTestWidget(ScreenToClientPoint(pt)) is not null;
        _window.SetClickThrough(!overWidget);
    }

    private (int X, int Y) ScreenToClientPoint(OverlayNative.POINT screen)
    {
        var p = screen;
        OverlayNative.ScreenToClient(_window.Handle, ref p);
        return (p.X, p.Y);
    }

    private string? HitTestWidget((int X, int Y) p)
    {
        foreach (var (rect, action) in _renderer.LegendRowRects)
            if (p.X >= rect.Left && p.X < rect.Right && p.Y >= rect.Top && p.Y < rect.Bottom)
                return action;
        return null;
    }

    private void OnOverlayClick(int clientX, int clientY)
    {
        var action = HitTestWidget((clientX, clientY));
        if (action is null) return;

        if (action == "menu-toggle")
        {
            _navMenuExpanded = !_navMenuExpanded;
        }
        else if (action.StartsWith("corner:", StringComparison.Ordinal))
        {
            _settings.NavMenuCorner = action.Substring("corner:".Length);
            _settings.Save();
        }
        else if (action.StartsWith("target:", StringComparison.Ordinal))
        {
            TogglePathTarget(action.Substring("target:".Length));
        }
    }

    private void BuildHpSpecs()
    {
        _hpSpecs.Clear();
        var hb = _settings.HpBars;
        foreach (var e in _entities)
        {
            if (!e.IsAlive || e.HpMax <= 0) continue;                 
            var on = e.Rarity switch                                   
            {
                Poe2Live.Rarity.Normal => _settings.HpBarNormal,
                Poe2Live.Rarity.Magic  => _settings.HpBarMagic,
                Poe2Live.Rarity.Rare   => _settings.HpBarRare,
                Poe2Live.Rarity.Unique => _settings.HpBarUnique,
                _                      => false,
            };
            if (!on) continue;
            var rule = _displayRules.Resolve(e);
            if (rule is null || rule.Hide) continue;                   
            var (bw, fillHex, borderW, borderHex) = e.Rarity switch    
            {
                Poe2Live.Rarity.Normal => (hb.WidthNormal, rule.Color, hb.BorderNormal, hb.BorderColorNormal),
                Poe2Live.Rarity.Magic  => (hb.WidthMagic,  rule.Color, hb.BorderMagic,  hb.BorderColorMagic),
                Poe2Live.Rarity.Rare   => (hb.WidthRare,   rule.Color, hb.BorderRare,   hb.BorderColorRare),
                Poe2Live.Rarity.Unique => (hb.WidthUnique, rule.Color, hb.BorderUnique, hb.BorderColorUnique),
                _                      => (0f, "#FFFFFF", 0f, "#FFFFFF"),
            };
            if (bw <= 0f) continue;
            _hpSpecs.Add(new HpBarSpec(e.Address, bw, PackColor(fillHex), borderW, PackColor(borderHex)));
        }
    }

    private static uint PackColor(string hex)
    {
        if (hex is { Length: >= 7 } && hex[0] == '#'
            && byte.TryParse(hex.AsSpan(1, 2), System.Globalization.NumberStyles.HexNumber, null, out var r)
            && byte.TryParse(hex.AsSpan(3, 2), System.Globalization.NumberStyles.HexNumber, null, out var g)
            && byte.TryParse(hex.AsSpan(5, 2), System.Globalization.NumberStyles.HexNumber, null, out var b))
            return 0xFF000000u | ((uint)r << 16) | ((uint)g << 8) | b;
        return 0xFFFFFFFFu;
    }

    private void HandleHotkeys()
    {
        if (Down(0x78)) { Console.WriteLine("\nF9 — exiting."); RequestShutdown(); }

        if (Down(0x7B) && DateTime.UtcNow >= _nextBrowserAt
            && _gameHwnd != 0 && GetForegroundWindow() == _gameHwnd)
        {
            _nextBrowserAt = DateTime.UtcNow.AddMilliseconds(800);
            OpenDashboard();
        }

        if (DateTime.UtcNow >= _nextPathKeyAt)
        {
            if (Down(AddNearestVk))
            {
                AddNearestPathTarget();
                _nextPathKeyAt = DateTime.UtcNow.AddMilliseconds(300);
            }
            else if (Down(ClearPathsVk))
            {
                ClearPathTargets();
                _nextPathKeyAt = DateTime.UtcNow.AddMilliseconds(300);
            }
        }

        if (Down(0x79) && DateTime.UtcNow >= _nextInspectAt) 
        {
            _nextInspectAt = DateTime.UtcNow.AddMilliseconds(250);
            AtlasRoutePick();
        }
    }

    private void AtlasRoutePick()
    {
        if (_inGameStateForApi == 0 || !GetCursorPos(out var pt)) { return; }
        var proj = AtlasProjection();
        double scaleX = Math.Abs(proj[0]) > 1e-6 ? proj[0] : 1, scaleY = Math.Abs(proj[4]) > 1e-6 ? proj[4] : 1;
        double curX = pt.X / scaleX, curY = pt.Y / scaleY; 

        Poe2Atlas.AtlasNodeLive? bestIn = null, bestAny = null; double bdIn = 1e18, bdAny = 1e18;
        foreach (var n in _atlas.ReadNodes(_inGameStateForApi))
        {
            if (!float.IsFinite(n.X) || !float.IsFinite(n.Y)) continue;
            double dx = curX - n.X, dy = curY - n.Y, d = dx * dx + dy * dy;
            if (d < bdAny) { bdAny = d; bestAny = n; }     
            double hw = (n.W > 1 ? n.W : 40) * 0.5, hh = (n.H > 1 ? n.H : 40) * 0.5; 
            if (Math.Abs(dx) <= hw && Math.Abs(dy) <= hh && d < bdIn) { bdIn = d; bestIn = n; } 
        }
        if ((bestIn ?? bestAny) is not { } b) { return; }

        if (_atlasStartGrid is null) { _atlasStartGrid = b.Grid; _atlasGoalGrid = null; }
        else if (_atlasGoalGrid is null) { _atlasGoalGrid = b.Grid; }
        else { _atlasStartGrid = null; _atlasGoalGrid = null; }
    }

    private double[] AtlasProjection()
    {
        float uiScale = _window.Height > 0 ? _window.Height / 1600f : 1080f / 1600f;
        float scale = uiScale * (_atlasZoom > 0.01f ? _atlasZoom : 0.85f);
        return new double[] { scale, 0, 0, 0, scale, 0, 0, 0 };
    }

    private List<NavTarget> BuildNavTargets(NumVec2 player)
    {
        var targets = new List<NavTarget>(_landmarks.Count + 16);
        var seen = new HashSet<string>();

        foreach (var lm in _landmarks)
        {
            var id = "t:" + lm.Key;
            if (!seen.Add(id)) continue;
            var autoPath = _displayRules.ResolveTile(lm.Path, requireMatch: false)?.Navigable ?? false;
            targets.Add(new NavTarget(id, LandmarkLabel(lm), lm.Center, lm.Path, IsEntity: false, AutoPath: autoPath));
        }

        var pois = _entities
            .Where(e => e.IsAlive && !e.IconComplete)
            .Select(e => (e, nav: _displayRules.Resolve(e)?.Navigable ?? false))
            .Where(x => x.e.Poi
                        || (x.e.Category == Poe2Live.EntityCategory.Monster && x.e.Rarity == Poe2Live.Rarity.Unique)
                        || x.nav)
            .OrderBy(x => NumVec2.DistanceSquared(x.e.Grid, player));
        foreach (var (e, nav) in pois)
        {
            var id = "e:" + e.Id;
            if (!seen.Add(id)) continue;
            targets.Add(new NavTarget(id, EntityLabel(e.Metadata), e.Grid, e.Metadata, IsEntity: true, AutoPath: nav));
        }

        return targets;
    }

    private void OnAreaChanged()
    {
        int count; bool restored;
        lock (_navLock)
        {
            if (_selectionAreaHash != 0) RememberZoneSelection(_selectionAreaHash, _selectedIds);

            _selectedIds.Clear();
            _selectionAreaHash = _areaHash;

            List<string>? remembered = null;
            restored = _areaHash != 0 && _zoneSelections.TryGetValue(_areaHash, out remembered);
            if (restored)
            {
                foreach (var id in remembered!)
                {
                    if (_selectedIds.Count >= MaxSelectedTargets) break;
                    if (!_selectedIds.Contains(id)) _selectedIds.Add(id);
                }
            }
            else
            {
                foreach (var t in _navTargets)
                {
                    if (_selectedIds.Count >= MaxSelectedTargets) break;
                    if (t.AutoPath && !_selectedIds.Contains(t.Id))
                        _selectedIds.Add(t.Id);
                }
            }
            count = _selectedIds.Count;
        }
        _selectedPaths = new List<SelectedPath>();
    }

    private void PruneCompletedTargets()
    {
        lock (_navLock)
        {
            if (_selectedIds.Count == 0) return;
            _selectedIds.RemoveAll(id =>
            {
                if (!id.StartsWith("e:", StringComparison.Ordinal) || !uint.TryParse(id.AsSpan(2), out var eid))
                    return false;
                foreach (var e in _entities)
                    if (e.Id == eid) return e.IconComplete; 
                return false; 
            });
        }
    }

    private void RememberZoneSelection(uint hash, List<string> ids)
    {
        if (!_zoneSelections.ContainsKey(hash))
        {
            if (_zoneOrder.Count >= MaxRememberedZones)
            {
                _zoneSelections.Remove(_zoneOrder[0]);
                _zoneOrder.RemoveAt(0);
            }
            _zoneOrder.Add(hash);
        }
        _zoneSelections[hash] = new List<string>(ids);
    }

    private string? TileLandmarkMatch(string tilePath)
    {
        var tr = _displayRules.ResolveTile(tilePath, requireMatch: true);
        return tr is { Hide: false } ? (tr.Label ?? "") : null;
    }

    private IReadOnlyList<string> CurrentTilePaths()
        => _areaInstanceForApi != 0 ? _live.TilePaths(_areaInstanceForApi) : Array.Empty<string>();

    private void AddNearestPathTarget()
    {
        if (_navTargets.Count == 0) return;
        var player = _state.Player;

        var selected = SnapshotSelection();
        var bestId = (string?)null;
        var bestD = float.MaxValue;
        foreach (var t in _navTargets)
        {
            if (selected.Contains(t.Id)) continue;
            var d = NumVec2.DistanceSquared(t.Grid, player);
            if (d < bestD) { d = bestD; bestId = t.Id; }
        }
        if (bestId is not null) ToggleSelectionCore(bestId); 
    }

    private void ClearPathTargets()
    {
        lock (_navLock)
        {
            _selectedIds.Clear();
        }
    }

    // ── Restored Delegate Targets For ApiServer Binding ──
    public IReadOnlyList<(string Id, int Slot)> GetNavSelection()
    {
        lock (_navLock)
        {
            var list = new List<(string, int)>(_selectedIds.Count);
            for (var i = 0; i < _selectedIds.Count; i++) list.Add((_selectedIds[i], i));
            return list;
        }
    }

    public void ToggleNavTarget(string id) => ToggleSelectionCore(id);

    public void ClearNavSelection()
    {
        lock (_navLock)
        {
            _selectedIds.Clear();
        }
    }

    private void TogglePathTarget(string id) => ToggleSelectionCore(id);

    private void ToggleSelectionCore(string id)
    {
        if (string.IsNullOrEmpty(id)) return;

        lock (_navLock)
        {
            if (_selectedIds.Remove(id)) return;
            if (_selectedIds.Count < MaxSelectedTargets) _selectedIds.Add(id);
        }
    }

    private List<string> SnapshotSelection()
    {
        lock (_navLock) return new List<string>(_selectedIds);
    }

    private void ReconcileTrackers(List<string> selected)
    {
        if (_trackers.Count > 0)
        {
            var live = new HashSet<string>(selected);
            var stale = _trackers.Keys.Where(k => !live.Contains(k)).ToList();
            foreach (var id in stale) _trackers.Remove(id);
        }

        foreach (var id in selected)
        {
            if (_trackers.ContainsKey(id)) continue;
            var tracker = new RouteTracker();
            _trackers[id] = tracker;
            if (TryResolveTargetGrid(id, out var grid))
                EnqueueReplan(id, tracker, grid);
        }
    }

    private bool TryResolveTargetGrid(string id, out NumVec2 grid)
    {
        grid = default;
        if (string.IsNullOrEmpty(id) || id.Length < 2) return false;

        if (id.StartsWith("t:", StringComparison.Ordinal))
        {
            var key = id[2..];
            foreach (var lm in _landmarks)
                if (lm.Key == key) { grid = lm.Center; return true; }
            return false;
        }

        if (id.StartsWith("e:", StringComparison.Ordinal))
        {
            if (!uint.TryParse(id[2..], out var entityId)) return false;
            foreach (var e in _entities)
                if (e.Id == entityId) { grid = e.Grid; return true; }
            return false;
        }

        return false;
    }

    private void MaintainRoutes(NumVec2 player)
    {
        var selected = SnapshotSelection();
        ReconcileTrackers(selected);

        foreach (var id in selected)
        {
            if (!_trackers.TryGetValue(id, out var tracker)) continue;
            tracker.Maintain(player);
            if (!TryResolveTargetGrid(id, out var goal)) continue;
            if (!tracker.ReplanInFlight && tracker.ShouldReplan(player, goal))
                EnqueueReplan(id, tracker, goal);
        }

        if (_replanner.TryDrainResults(out var results))
        {
            foreach (var r in results)
            {
                if (!_trackers.TryGetValue(r.TargetId, out var tracker)) continue; 
                tracker.ApplyResult(r.Waypoints, new NumVec2(r.Goal.x, r.Goal.y));
            }
        }

        RebuildSelectedPaths(selected);
    }

    private void EnqueueReplan(string id, RouteTracker tracker, NumVec2 goal)
    {
        if (_terrain is not { } terrain) return; 
        var player = _state.Player;
        tracker.MarkReplanRequested();
        _replanner.Enqueue(new BackgroundReplanner.Request(
            id, terrain, ((int)player.X, (int)player.Y), ((int)goal.X, (int)goal.Y)));
    }

    private void RebuildSelectedPaths(List<string> selected)
    {
        var paths = new List<SelectedPath>(selected.Count);
        for (var i = 0; i < selected.Count; i++)
        {
            if (!_trackers.TryGetValue(selected[i], out var tracker)) continue;
            var pts = tracker.CurrentPoints;
            if (pts.Count > 0) paths.Add(new SelectedPath(Math.Min(i, MaxSelectedTargets - 1), pts));
        }
        _selectedPaths = paths;
    }

    private string TargetLabel(string id)
    {
        foreach (var t in _navTargets) if (t.Id == id) return t.Name;
        return id;
    }

    private string LandmarkLabel(Poe2Live.Landmark lm)
        => _settings.UseCuratedLandmarks && lm.CuratedName is { } c ? c : lm.Name;

    private static string EntityLabel(string metadata)
    {
        if (string.IsNullOrEmpty(metadata)) return "(entity)";

        if (EntityNameResolver.Shared.Resolve(metadata) is { Length: > 0 } resolved)
            return resolved;

        var slash = metadata.LastIndexOf('/');
        var seg = slash >= 0 ? metadata[(slash + 1)..] : metadata;

        var end = seg.Length;
        while (end > 0 && char.IsDigit(seg[end - 1])) end--;
        if (end > 0 && seg[end - 1] == '_') end--;
        if (end > 0) seg = seg[..end];

        var sb = new System.Text.StringBuilder(seg.Length + 8);
        for (var i = 0; i < seg.Length; i++)
        {
            var ch = seg[i];
            if (i > 0)
            {
                var prev = seg[i - 1];
                var boundary = (char.IsUpper(ch) && (char.IsLower(prev) || char.IsDigit(prev)))
                               || (char.IsDigit(ch) && char.IsLetter(prev) && !char.IsDigit(prev));
                if (boundary && sb.Length > 0 && sb[^1] != ' ') sb.Append(' ');
            }
            sb.Append(ch);
        }
        var label = sb.ToString().Trim();
        return label.Length == 0 ? "(entity)" : label;
    }

    private List<LegendEntry> BuildLegend(List<string> selected)
    {
        var legend = new List<LegendEntry>(_navTargets.Count);
        foreach (var t in _navTargets)
        {
            var slot = selected.IndexOf(t.Id);
            legend.Add(new LegendEntry(t, slot, slot >= 0));
        }
        return legend;
    }

    private unsafe object AtlasJson()
    {
        var d = _atlas.Read(_lastAreaInstance);
        var nodes = _inGameStateForApi != 0 ? _atlas.ReadNodes(_inGameStateForApi) : new List<Poe2Atlas.AtlasNodeLive>();
        var vis = nodes.Where(n => n.Visible).ToList();
        return new
        {
            located = d.Located,
            note = d.Note,
            catalogAddr = $"0x{d.CatalogAddr:X}",
            catalogCount = d.CatalogCount,
            regionCount = d.Region.Count,
            catalog = d.Catalog.Select(m => new { id = m.Id, code = m.Code, name = m.Name, kind = m.Kind, parsedObj = $"0x{m.ParsedObj:X}" }),
            region = d.Region.Select(r => new { code = r.Code, name = r.Name, kind = r.Kind }),
            nodes = new
            {
                total = nodes.Count,
                visible = vis.Count,
                hasContent = nodes.Count(n => n.HasContent),
                unvisited = nodes.Count(n => !n.Visited),
                unlocked = nodes.Count(n => n.Unlocked),
                biomes = nodes.GroupBy(n => (int)n.Biome).OrderBy(g => g.Key).ToDictionary(g => g.Key.ToString(), g => g.Count()),
            },
            allTags = nodes.SelectMany(n => n.Tags).GroupBy(t => t).OrderByDescending(g => g.Count())
                .Select(g => new { tag = g.Key, count = g.Count() }),
            allMaps = nodes.Where(n => !string.IsNullOrEmpty(n.MapName)).GroupBy(n => n.MapName)
                .OrderBy(g => g.Key).Select(g => new { tag = g.Key, count = g.Count() }),
            highlightTags = _settings.AtlasHighlightTags,
            arrowTags = _settings.AtlasArrowTags,
            nodeList = nodes
                .OrderByDescending(n => n.Visible).ThenByDescending(n => n.HasContent).ThenByDescending(n => !n.Visited)
                .Take(2000)
                .Select(n => new
                {
                    el = ((long)n.Element).ToString(), 
                    id = n.Id, biome = (int)n.Biome, type = n.IconType, hasContent = n.HasContent,
                    unlocked = n.Unlocked, visited = n.Visited, visible = n.Visible,
                    x = (int)n.X, y = (int)n.Y, map = n.MapName, tags = n.Tags,
                }),
        };
    }

    private void UpdateAtlas(nint inGameState)
    {
        var nodes = _atlas.ReadNodes(inGameState);
        if (nodes.Count == 0)
        {
            var stillOpen = _atlas.IsAtlasOpen(inGameState) || (DateTime.UtcNow - _atlasGoodAt).TotalSeconds < 0.4;
            if (_atlasOpen && stillOpen) return;             
            _atlasOpen = false; _builtAtlasOnce = false; _lastAtlasSig = 0;   
            if (_atlasMarks.Count > 0) _atlasMarks = new();
            _atlasRoute = new(); _atlasStartPt = _atlasEndPt = null;   
            return;
        }
        _atlasGoodAt = DateTime.UtcNow;
        _atlasOpen = true;
        var scales = nodes.Where(n => n.Scale > 0.01f).Select(n => n.Scale).OrderBy(s => s).ToList();
        if (scales.Count > 0) _atlasZoom = scales[scales.Count / 2];

        float pscale = (_window.Height > 0 ? _window.Height / 1600f : 0.675f) * (_atlasZoom > 0.01f ? _atlasZoom : 0.85f);
        double cxSum = 0, cySum = 0; int onCount = 0; float vw = _window.Width, vh = _window.Height; const float vm = 80f;
        foreach (var n in nodes)
        {
            float sx = n.X * pscale, sy = n.Y * pscale;
            if (sx > vm && sx < vw - vm && sy > vm && sy < vh - vm) { cxSum += n.X; cySum += n.Y; onCount++; }
        }
        long viewSig = onCount == 0 ? 0
            : (long)Math.Round(cxSum / onCount) * 73856093L
            ^ (long)Math.Round(cySum / onCount) * 19349663L
            ^ (long)Math.Round(_atlasZoom * 2000f) * 83492791L;
        int selCnt; lock (_atlasLock) selCnt = _atlasSel.Count;
        long inputSig = (long)(_atlasStartGrid?.GetHashCode() ?? 0)
            ^ ((long)(_atlasGoalGrid?.GetHashCode() ?? 0) << 1)
            ^ ((long)(_settings.AtlasHighlightTags?.Count ?? 0) << 20)
            ^ ((long)(_settings.AtlasArrowTags?.Count ?? 0) << 28)
            ^ ((long)selCnt << 36)
            ^ (_settings.AtlasDrawAll ? 1L << 44 : 0L);
        long sig = viewSig * 2654435761L ^ inputSig;
        if (_builtAtlasOnce && _atlas.AllTagsResolved && sig == _lastAtlasSig)
            return;   
        _lastAtlasSig = sig; _builtAtlasOnce = true;

        HashSet<nint> sel; lock (_atlasLock) sel = new HashSet<nint>(_atlasSel);

        var hlTrack = new HashSet<string>(_settings.AtlasHighlightTags ?? new(), StringComparer.OrdinalIgnoreCase);
        var hlArrow = new HashSet<string>(_settings.AtlasArrowTags ?? new(), StringComparer.OrdinalIgnoreCase);
        static string? Match(HashSet<string> set, in Poe2Atlas.AtlasNodeLive nd)
        {
            if (set.Count == 0) return null;
            if (!string.IsNullOrEmpty(nd.MapName) && set.Contains(nd.MapName)) return nd.MapName;
            if (nd.Tags is { Count: > 0 }) foreach (var t in nd.Tags) if (set.Contains(t)) return t;
            return null;
        }
        var marks = new List<AtlasMark>(128);
        foreach (var n in nodes)
        {
            var selected = sel.Contains(n.Element);
            var mTrack = Match(hlTrack, n);
            var mArrow = Match(hlArrow, n);
            var isTracked = selected || mTrack != null;
            var isArrow = mArrow != null;
            if (!_settings.AtlasDrawAll && !isTracked && !isArrow) continue;
            var matched = mTrack ?? mArrow;
            var label = matched ?? (n.Tags is { Count: > 0 } ? n.Tags[0] : (string.IsNullOrEmpty(n.MapName) ? null : n.MapName));
            string? color = matched != null && _settings.AtlasHighlightColors.TryGetValue(matched, out var c) ? c : null;
            marks.Add(new AtlasMark(n.X, n.Y, isTracked, n.HasContent, n.Visited, n.Unlocked, n.Biome, n.IconType, label, color, isArrow));
        }
        _atlasMarks = marks;
        BuildAtlasRoute(nodes);
    }

    private void BuildAtlasRoute(IReadOnlyList<Poe2Atlas.AtlasNodeLive> nodes)
    {
        _atlasRoute = new(); _atlasStartPt = null; _atlasEndPt = null;
        if (nodes.Count == 0) return;

        var gridToRel = new Dictionary<(int, int), NumVec2>(nodes.Count);
        foreach (var n in nodes) gridToRel[n.Grid] = new NumVec2(n.X, n.Y);

        if (_atlasStartGrid is { } s && gridToRel.TryGetValue(s, out var sp)) _atlasStartPt = sp;
        if (_atlasGoalGrid is { } g && gridToRel.TryGetValue(g, out var gp)) _atlasEndPt = gp;

        if (_atlasStartGrid is { } start && _atlasGoalGrid is { } goal)
        {
            var path = _atlas.FindPath(start, goal);
            if (path != null) foreach (var p in path) if (gridToRel.TryGetValue(p, out var rp)) _atlasRoute.Add(rp);
        }
    }

    public void SetAtlasSelection(IReadOnlyList<long> els)
    {
        lock (_atlasLock) { _atlasSel.Clear(); foreach (var e in els) _atlasSel.Add((nint)e); }
    }

    public void SetAtlasHighlight(IReadOnlyList<(string tag, string color, bool track, bool arrow)> rules)
    {
        var tags = new List<string>(); var arrows = new List<string>();
        var colors = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        var seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var (tag, color, track, arrow) in rules)
        {
            if (string.IsNullOrWhiteSpace(tag) || !seen.Add(tag)) continue;
            if (track) tags.Add(tag);
            if (arrow) arrows.Add(tag);
            if (!string.IsNullOrWhiteSpace(color)) colors[tag] = color;
        }
        _settings.AtlasHighlightTags = tags;
        _settings.AtlasArrowTags = arrows;
        _settings.AtlasHighlightColors = colors;
        _settings.AtlasRulesInitialized = true;   
        _settings.Save();
    }

    private void OpenDashboard()
    {
        var url = $"http://localhost:{_settings.ApiPort}/";
        try
        {
            System.Diagnostics.Process.Start(new System.Diagnostics.ProcessStartInfo(url) { UseShellExecute = true });
        }
        catch (Exception ex) { Console.Error.WriteLine($"Open dashboard failed: {ex.Message}"); }
    }

    private static bool Down(int vk) => (GetAsyncKeyState(vk) & 0x8000) != 0;

    [DllImport("user32.dll")]
    private static extern short GetAsyncKeyState(int vKey);

    [DllImport("user32.dll")]
    private static extern nint GetForegroundWindow();

    [StructLayout(LayoutKind.Sequential)] private struct CursorPoint { public int X, Y; }
    [DllImport("user32.dll")] private static extern bool GetCursorPos(out CursorPoint p);

    public void Dispose()
    {
        _replanner.Dispose();
        _api.Dispose();
        _renderer.Dispose();
        _window.Dispose();
    }
}
