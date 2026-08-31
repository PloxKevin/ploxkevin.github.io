const PLANNER_STORAGE = {
  plan: "kord-breach:raid-plan:v1",
  map: "kord-breach:planner-map",
  regularActive: "kord-breach:regular-active",
  regularCompleted: "kord-breach:regular-completed",
  external: "kord-breach:external-quest-status",
  storylineActive: "kord-breach:active",
  storylineCompleted: "kord-breach:completed",
  playerLevel: "kord-breach:player-level",
  faction: "kord-breach:player-faction",
  reputation: "kord-breach:trader-reputation",
  route: "kord-breach:route",
};

const progressionRules = window.KordProgressionRules;

const MAP_ORDER = [
  "ground-zero",
  "streets-of-tarkov",
  "customs",
  "woods",
  "shoreline",
  "interchange",
  "reserve",
  "lighthouse",
  "factory",
  "the-lab",
  "the-labyrinth",
  "icebreaker",
  "anywhere",
];

const plannerState = {
  regular: null,
  storyline: null,
  mapConfig: null,
  kordIntel: { tasks: {} },
  maps: [],
  configBySlug: new Map(),
  aliasToSlug: new Map(),
  mapIdToSlug: new Map(),
  selectedMap: "shoreline",
  filters: {
    search: "",
    readiness: "open",
    source: "all",
    pinMode: "all",
  },
  plan: readPlan(),
  rows: [],
  visibleRows: [],
  clusters: [],
  selectedCluster: null,
  selectedMarkerId: null,
  expandedTaskKeys: new Set(),
  focusedTaskKey: null,
  zoom: 1,
  mapAspect: 1.5,
  renderedMap: null,
  artworkToken: 0,
  mapLayerBySlug: new Map(),
};

const plannerDom = {};
const wikiPreviewCache = new Map();
let plannerToastTimer;
let plannerSearchTimer;
let wikiHoverTimer;
let wikiHideTimer;
let wikiRequestToken = 0;
let activeWikiTrigger = null;
let mapDrag = null;

document.addEventListener("DOMContentLoaded", initializePlanner);

async function initializePlanner() {
  cachePlannerDom();
  bindPlannerEvents();
  setPlannerControlsDisabled(true);

  try {
    const [regular, storyline, mapConfig, kordIntel] = await Promise.all([
      fetchJson("./data/regular_quest_progression.json"),
      fetchJson("./data/kord_breach_quests.json"),
      fetchJson("./data/map-config.json"),
      fetchJson("./data/kord-map-intel.json").catch(() => ({ tasks: {} })),
    ]);

    regular.tasks = (regular.tasks || []).filter((task) => !task.hiddenFromTracker);
    plannerState.regular = regular;
    plannerState.storyline = storyline;
    plannerState.mapConfig = mapConfig;
    plannerState.kordIntel = kordIntel;
    prepareMapIndexes();
    validateStoredPlan();
    hydrateMapSelector();
    applyInitialRoute();
    setPlannerControlsDisabled(false);
    renderPlanner({ mapChanged: true });

    plannerDom.plannerSnapshot.textContent = `Snapshot ${formatDate(regular.meta?.generatedAt || regular.meta?.researchedAt)}`;
  } catch (error) {
    plannerDom.plannerStatus.textContent = "Raid intelligence failed to load.";
    plannerDom.objectiveList.innerHTML =
      '<div class="empty-state"><strong>Map data unavailable</strong><p>Run the static build so quest geometry and map calibration are included.</p></div>';
    console.error(error);
  }
}

async function fetchJson(path) {
  const response = await fetch(path);
  if (!response.ok) throw new Error(`${path} returned ${response.status}`);
  return response.json();
}

function cachePlannerDom() {
  const ids = [
    "clear-planner-filters",
    "clear-raid-plan",
    "close-wiki-preview",
    "exact-pin-total",
    "map-artwork",
    "map-fallback-label",
    "map-heading",
    "map-kicker",
    "map-layer",
    "map-layer-control",
    "map-reset",
    "map-source-link",
    "map-stage",
    "map-subtitle",
    "map-viewport",
    "map-zoom-in",
    "map-zoom-level",
    "map-zoom-out",
    "marker-detail",
    "marker-layer",
    "objective-list",
    "planner-empty",
    "planner-map",
    "planner-pin-mode",
    "planner-readiness",
    "planner-search",
    "planner-snapshot",
    "planner-source",
    "planner-status",
    "planner-toast",
    "pool-count",
    "raid-plan-empty",
    "raid-plan-heading",
    "raid-plan-intro",
    "raid-plan-list",
    "raid-plan-total",
    "visible-task-total",
    "wiki-hover-preview",
    "wiki-preview-body",
    "wiki-preview-title",
  ];

  for (const id of ids) {
    const key = id.replace(/-([a-z])/g, (_, character) => character.toUpperCase());
    plannerDom[key] = document.getElementById(id);
  }
}

function bindPlannerEvents() {
  plannerDom.plannerMap.addEventListener("change", () => {
    plannerState.selectedMap = plannerDom.plannerMap.value;
    plannerState.focusedTaskKey = null;
    plannerState.selectedCluster = null;
    plannerState.selectedMarkerId = null;
    plannerState.zoom = 1;
    plannerState.renderedMap = null;
    writeValue(PLANNER_STORAGE.map, plannerState.selectedMap);
    updatePlannerUrl({ clearTask: true });
    renderPlanner({ mapChanged: true });
  });

  plannerDom.plannerSearch.addEventListener("input", () => {
    window.clearTimeout(plannerSearchTimer);
    plannerSearchTimer = window.setTimeout(() => {
      plannerState.filters.search = plannerDom.plannerSearch.value.trim().toLowerCase();
      renderPlanner();
    }, 90);
  });

  plannerDom.plannerReadiness.addEventListener("change", () => {
    plannerState.filters.readiness = plannerDom.plannerReadiness.value;
    renderPlanner();
  });

  plannerDom.plannerSource.addEventListener("change", () => {
    plannerState.filters.source = plannerDom.plannerSource.value;
    updatePlannerUrl();
    renderPlanner();
  });

  plannerDom.plannerPinMode.addEventListener("change", () => {
    plannerState.filters.pinMode = plannerDom.plannerPinMode.value;
    renderMarkers();
    updatePlannerSummary();
  });

  plannerDom.clearPlannerFilters.addEventListener("click", () => {
    plannerState.filters = { search: "", readiness: "open", source: "all", pinMode: "all" };
    plannerState.focusedTaskKey = null;
    plannerDom.plannerSearch.value = "";
    plannerDom.plannerReadiness.value = "open";
    plannerDom.plannerSource.value = "all";
    plannerDom.plannerPinMode.value = "all";
    updatePlannerUrl({ clearTask: true });
    renderPlanner();
  });

  plannerDom.objectiveList.addEventListener("click", handleTaskPoolClick);
  plannerDom.objectiveList.addEventListener("toggle", handleTaskPoolToggle, true);
  plannerDom.markerDetail.addEventListener("click", handleMarkerDetailClick);
  plannerDom.raidPlanList.addEventListener("click", handleRaidPlanClick);

  plannerDom.clearRaidPlan.addEventListener("click", () => {
    const currentPlan = currentRaidEntries();
    const mapName = plannerState.configBySlug.get(plannerState.selectedMap)?.name || "this location";
    if (!currentPlan.length || !window.confirm(`Clear every quest from the ${mapName} raid plan?`)) return;
    plannerState.plan = plannerState.plan.filter((entry) => entry.mapSlug !== plannerState.selectedMap);
    persistPlan();
    renderPlanner();
    showPlannerToast(`${mapName} raid cleared.`);
  });

  plannerDom.mapZoomIn.addEventListener("click", () => setMapZoom(plannerState.zoom + 0.25));
  plannerDom.mapZoomOut.addEventListener("click", () => setMapZoom(plannerState.zoom - 0.25));
  plannerDom.mapReset.addEventListener("click", resetMapView);
  plannerDom.mapLayer.addEventListener("change", () => {
    plannerState.mapLayerBySlug.set(plannerState.selectedMap, plannerDom.mapLayer.value);
    plannerState.renderedMap = null;
    renderPlanner({ mapChanged: true });
  });
  plannerDom.mapViewport.addEventListener("keydown", handleMapKeyboard);
  plannerDom.mapViewport.addEventListener("pointerdown", beginMapDrag);
  plannerDom.mapViewport.addEventListener("pointermove", continueMapDrag);
  plannerDom.mapViewport.addEventListener("pointerup", endMapDrag);
  plannerDom.mapViewport.addEventListener("pointercancel", endMapDrag);

  plannerDom.markerLayer.addEventListener("click", (event) => {
    const marker = event.target.closest("[data-cluster-index]");
    if (!marker) return;
    const index = Number(marker.dataset.clusterIndex);
    selectCluster(index, { center: false });
    queueWikiPreview(index, 0, { trigger: marker, focusPreview: event.detail === 0 });
  });
  plannerDom.markerLayer.addEventListener("pointerover", handleMarkerPointerOver);
  plannerDom.markerLayer.addEventListener("pointerout", handleMarkerPointerOut);
  plannerDom.markerLayer.addEventListener("focusin", (event) => {
    const marker = event.target.closest("[data-cluster-index]");
    if (marker) queueWikiPreview(Number(marker.dataset.clusterIndex), 0, { trigger: marker });
  });
  plannerDom.markerLayer.addEventListener("focusout", () => {
    window.setTimeout(() => {
      if (!plannerDom.markerLayer.contains(document.activeElement) &&
        !plannerDom.wikiHoverPreview.contains(document.activeElement)) scheduleWikiHide();
    }, 0);
  });

  plannerDom.wikiHoverPreview.addEventListener("pointerenter", cancelWikiHide);
  plannerDom.wikiHoverPreview.addEventListener("pointerleave", scheduleWikiHide);
  plannerDom.wikiHoverPreview.addEventListener("focusin", cancelWikiHide);
  plannerDom.wikiHoverPreview.addEventListener("focusout", () => {
    window.setTimeout(() => {
      if (!plannerDom.wikiHoverPreview.contains(document.activeElement)) scheduleWikiHide();
    }, 0);
  });
  plannerDom.closeWikiPreview.addEventListener("click", () => hideWikiPreview({ restoreFocus: true }));
  document.addEventListener("keydown", (event) => {
    if (event.key !== "Escape" || plannerDom.wikiHoverPreview.hidden) return;
    event.preventDefault();
    hideWikiPreview({ restoreFocus: true });
  });

  window.addEventListener("resize", () => applyMapGeometry({ preserveCenter: true }));
}

function setPlannerControlsDisabled(disabled) {
  for (const control of [
    plannerDom.plannerMap,
    plannerDom.plannerSearch,
    plannerDom.plannerReadiness,
    plannerDom.plannerSource,
    plannerDom.plannerPinMode,
    plannerDom.mapLayer,
    plannerDom.clearPlannerFilters,
  ]) {
    control.disabled = disabled;
  }
}

function prepareMapIndexes() {
  plannerState.maps = (plannerState.mapConfig.maps || []).map((config) => ({ ...config }));
  plannerState.configBySlug.clear();
  plannerState.aliasToSlug.clear();
  plannerState.mapIdToSlug.clear();

  for (const config of plannerState.maps) {
    plannerState.configBySlug.set(config.slug, config);
    for (const alias of [config.slug, config.name, ...(config.aliases || [])]) {
      plannerState.aliasToSlug.set(looseSlug(alias), config.slug);
    }
  }

  const discoveredNames = new Set();
  for (const task of plannerState.regular.tasks || []) {
    if (task.map) {
      const slug = mapSlug(task.map.normalizedName || task.map.name);
      plannerState.mapIdToSlug.set(task.map.id, slug);
      discoveredNames.add(task.map.name);
    }
    for (const objective of task.objectives || []) {
      for (const map of objective.maps || []) {
        const slug = mapSlug(map.normalizedName || map.name);
        plannerState.mapIdToSlug.set(map.id, slug);
        discoveredNames.add(map.name);
      }
      for (const location of objective.locations || []) {
        if (location.mapName) discoveredNames.add(location.mapName);
      }
    }
  }

  for (const name of discoveredNames) {
    const slug = mapSlug(name);
    if (!slug || plannerState.configBySlug.has(slug)) continue;
    const config = {
      slug,
      name,
      aliases: [],
      bounds: null,
      image: null,
      basemapSupported: false,
      calibrationSupported: false,
      unsupportedReason: "No calibrated community basemap is available for this seasonal location.",
    };
    plannerState.maps.push(config);
    plannerState.configBySlug.set(slug, config);
    plannerState.aliasToSlug.set(looseSlug(name), slug);
  }

  const anywhere = {
    slug: "anywhere",
    name: "Any map / off-raid",
    aliases: ["Hideout", "Unmapped"],
    bounds: null,
    image: null,
    basemapSupported: false,
    calibrationSupported: false,
    unsupportedReason: "These objectives do not expose one fixed raid coordinate.",
  };
  plannerState.maps.push(anywhere);
  plannerState.configBySlug.set(anywhere.slug, anywhere);
  plannerState.aliasToSlug.set("hideout", anywhere.slug);
  plannerState.aliasToSlug.set("any-map", anywhere.slug);
  plannerState.aliasToSlug.set("anywhere", anywhere.slug);

  for (const task of plannerState.regular.tasks || []) {
    if (task.map?.id) plannerState.mapIdToSlug.set(task.map.id, mapSlug(task.map.name));
    for (const objective of task.objectives || []) {
      for (const map of objective.maps || []) {
        if (map.id) plannerState.mapIdToSlug.set(map.id, mapSlug(map.name));
      }
      for (const location of objective.locations || []) {
        if (location.mapId && location.mapName) {
          plannerState.mapIdToSlug.set(location.mapId, mapSlug(location.mapName));
        }
      }
    }
  }

  plannerState.maps.sort((a, b) => {
    const aRank = MAP_ORDER.indexOf(a.slug);
    const bRank = MAP_ORDER.indexOf(b.slug);
    return (aRank < 0 ? MAP_ORDER.length : aRank) -
      (bRank < 0 ? MAP_ORDER.length : bRank) || a.name.localeCompare(b.name);
  });
}

function hydrateMapSelector() {
  plannerDom.plannerMap.innerHTML = plannerState.maps
    .map((map) => `<option value="${escapePlanner(map.slug)}">${escapePlanner(map.name)}</option>`)
    .join("");
}

function applyInitialRoute() {
  const params = new URLSearchParams(window.location.search);
  const source = ["regular", "storyline"].includes(params.get("source")) ? params.get("source") : null;
  const taskId = params.get("task");
  const taskKey = source && taskId ? `${source}:${taskId}` : null;
  const queryMap = params.get("map");
  const storedMap = readValue(PLANNER_STORAGE.map, "");
  const inferredMap = taskKey ? firstMapForTask(source, taskId) : null;
  const requestedMap = queryMap ? mapSlug(queryMap) : inferredMap || mapSlug(storedMap);

  plannerState.selectedMap = plannerState.configBySlug.has(requestedMap)
    ? requestedMap
    : plannerState.configBySlug.has("shoreline")
      ? "shoreline"
      : plannerState.maps[0]?.slug || "anywhere";
  plannerState.focusedTaskKey = taskKey;
  plannerState.filters.source = source || "all";
  if (taskKey) plannerState.filters.readiness = "all";

  plannerDom.plannerMap.value = plannerState.selectedMap;
  plannerDom.plannerSource.value = plannerState.filters.source;
  plannerDom.plannerReadiness.value = plannerState.filters.readiness;
  plannerDom.plannerPinMode.value = plannerState.filters.pinMode;
}

function firstMapForTask(source, taskId) {
  if (source === "regular") {
    const task = plannerState.regular.tasks.find((item) => item.id === taskId);
    if (!task) return null;
    for (const objective of task.objectives || []) {
      const location = (objective.locations || [])[0];
      if (location) return locationMapSlug(location);
      const map = (objective.maps || [])[0];
      if (map) return mapSlug(map.normalizedName || map.name);
    }
    return task.map ? mapSlug(task.map.normalizedName || task.map.name) : "anywhere";
  }

  const quest = plannerState.storyline.quests.find((item) => item.id === taskId);
  return quest ? questMapSlugs(quest)[0] || "anywhere" : null;
}

function renderPlanner(options = {}) {
  const regularRows = buildRegularRows(plannerState.selectedMap);
  const storylineRows = buildStorylineRows(plannerState.selectedMap);
  plannerState.rows = [...storylineRows, ...regularRows];
  plannerState.visibleRows = plannerState.rows.filter(matchesPlannerFilters).sort(comparePlannerRows);

  renderTaskPool();
  renderRaidPlan();
  renderMap(options);
  updatePlannerSummary();
  focusDeepLinkedTask();
}

function buildRegularRows(selectedMap) {
  const context = buildRegularAvailabilityContext();
  const rows = [];

  for (const task of plannerState.regular.tasks || []) {
    const objectives = [];
    const sourceObjectives = task.objectives?.length
      ? task.objectives
      : [{
          id: `${task.id}-task`,
          type: "task",
          description: "Open the quest reference for objective details.",
          optional: false,
          maps: task.map ? [task.map] : [],
          locations: [],
        }];

    for (let index = 0; index < sourceObjectives.length; index += 1) {
      const objective = sourceObjectives[index];
      const ownMapSlugs = new Set((objective.maps || []).map((map) => mapSlug(map.normalizedName || map.name)));
      const locations = uniqueExactLocations((objective.locations || []).filter(
        (location) => locationMapSlug(location) === selectedMap,
      ));
      const taskMap = task.map ? mapSlug(task.map.normalizedName || task.map.name) : null;
      const hasAnyObjectiveMap = (objective.maps || []).length > 0 || (objective.locations || []).length > 0;
      const relevant = selectedMap === "anywhere"
        ? !taskMap && !hasAnyObjectiveMap
        : locations.length > 0 || ownMapSlugs.has(selectedMap) || (!hasAnyObjectiveMap && taskMap === selectedMap);

      if (!relevant) continue;

      const markers = locations
        .filter(hasFinitePosition)
        .map((location, locationIndex) => ({
          id: `regular:${task.id}:${objective.id}:${locationIndex}`,
          rowKey: `regular:${task.id}`,
          objectiveIndex: index,
          taskName: task.name,
          trader: task.traderName,
          source: "regular",
          wikiLink: task.wikiLink,
          description: objective.description,
          label: location.kind === "spawn" ? "Possible quest-item spawn" : "Objective zone",
          detail: location.kind === "spawn"
            ? "Possible spawn position from current seasonal game data."
            : "Objective-zone center from current seasonal game data.",
          confidence: "exact",
          kind: location.kind,
          position: { x: Number(location.x), y: Number(location.y), z: Number(location.z) },
          top: finiteOrNull(location.top),
          bottom: finiteOrNull(location.bottom),
        }));
      markers.push(...curatedApproximateMarkers(selectedMap, task, objective, index));

      objectives.push({
        id: objective.id,
        index,
        type: objective.type,
        description: objective.description || "Unnamed objective",
        optional: Boolean(objective.optional),
        markers,
        quality: markers.some((marker) => marker.confidence === "exact")
          ? "exact"
          : markers.some((marker) => marker.confidence === "approximate")
            ? "approximate"
            : "map-level",
      });
    }

    if (!objectives.length) continue;
    const availability = getRegularAvailability(task, context);
    rows.push({
      key: `regular:${task.id}`,
      source: "regular",
      taskId: task.id,
      name: task.name,
      trader: task.traderName,
      wikiLink: task.wikiLink,
      mapSlug: selectedMap,
      status: availability.status,
      statusLabel: availability.status === "done"
        ? "Completed"
        : availability.status === "active"
          ? "Active in game"
          : availability.status === "available"
            ? "Modeled available"
            : "Plan ahead",
      reasons: availability.status === "active" ? availability.modeledReasons : availability.reasons,
      reasonHeading: availability.status === "active" ? "Model estimate differs" : "Not ready yet",
      objectives,
      markers: objectives.flatMap((objective) => objective.markers),
    });
  }

  return rows;
}

function curatedApproximateMarkers(mapSlugValue, task, objective, objectiveIndex) {
  const pins = plannerState.configBySlug.get(mapSlugValue)?.approximatePins || [];
  const description = String(objective.description || "").toLowerCase();
  return pins
    .filter((pin) => pin.taskName === task.name && description.includes(String(pin.objectiveIncludes || "").toLowerCase()))
    .map((pin, pinIndex) => ({
      id: `regular:${task.id}:${objective.id}:approximate:${pinIndex}`,
      rowKey: `regular:${task.id}`,
      objectiveIndex,
      taskName: task.name,
      trader: task.traderName,
      source: "regular",
      wikiLink: task.wikiLink,
      description: objective.description,
      label: pin.label,
      detail: pin.detail,
      confidence: "approximate",
      kind: "curated-approximation",
      position: { left: Number(pin.left), top: Number(pin.top), y: null },
      floorLabel: pin.floorLabel || null,
      top: null,
      bottom: null,
    }));
}

function uniqueExactLocations(locations) {
  const seen = new Set();
  return locations.filter((location) => {
    const key = [
      location.kind || "position",
      location.zoneId || "",
      location.x,
      location.y,
      location.z,
      location.top ?? "",
      location.bottom ?? "",
    ].join(":");
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

function buildStorylineRows(selectedMap) {
  const rows = [];
  const context = buildStorylineAvailabilityContext();

  for (const quest of plannerState.storyline.quests || []) {
    const intelligence = plannerState.kordIntel.tasks?.[quest.id] || [];
    const objectives = [];

    for (let index = 0; index < (quest.objectives || []).length; index += 1) {
      const description = quest.objectives[index];
      const entries = intelligence.filter(
        (entry) => Number(entry.objectiveIndex) === index && entry.mapSlug === selectedMap,
      );
      const objectiveSlugs = storyObjectiveSlugs(quest, description, index, intelligence);
      const relevant = selectedMap === "anywhere"
        ? objectiveSlugs.includes("anywhere")
        : entries.length > 0 || objectiveSlugs.includes(selectedMap);
      if (!relevant) continue;

      const markers = entries
        .filter((entry) => hasFinitePosition(entry.position))
        .map((entry, entryIndex) => ({
          id: `storyline:${quest.id}:${index}:${entryIndex}`,
          rowKey: `storyline:${quest.id}`,
          objectiveIndex: index,
          taskName: quest.name,
          trader: quest.trader,
          source: "storyline",
          wikiLink: quest.source_url,
          description,
          label: entry.label,
          detail: entry.detail,
          confidence: "poi",
          kind: "named-poi",
          position: { x: Number(entry.position.x), y: null, z: Number(entry.position.z) },
          top: null,
          bottom: null,
        }));

      objectives.push({
        id: `${quest.id}-${index}`,
        index,
        type: "storyline",
        description,
        optional: /^optional:/i.test(description),
        markers,
        quality: markers.length ? "poi" : "map-level",
      });
    }

    if (!objectives.length) continue;
    const availability = getStorylineAvailability(quest, context);
    rows.push({
      key: `storyline:${quest.id}`,
      source: "storyline",
      taskId: quest.id,
      name: quest.name,
      trader: quest.trader,
      wikiLink: quest.source_url,
      mapSlug: selectedMap,
      status: availability.status,
      statusLabel: availability.label,
      reasons: availability.reasons,
      reasonHeading: availability.status === "active" ? "Model estimate differs" : "Not ready yet",
      objectives,
      markers: objectives.flatMap((objective) => objective.markers),
    });
  }

  return rows;
}

function storyObjectiveSlugs(quest, description, index, intelligence) {
  const explicit = new Set(
    intelligence
      .filter((entry) => Number(entry.objectiveIndex) === index)
      .map((entry) => entry.mapSlug),
  );
  if (explicit.size) return [...explicit];
  const questMaps = questMapSlugs(quest);
  const allowedMaps = new Set(questMaps);
  const text = description.toLowerCase();
  for (const config of plannerState.maps) {
    if (config.slug === "anywhere" || !allowedMaps.has(config.slug)) continue;
    const aliases = [config.name, ...(config.aliases || [])]
      .map((name) => String(name).toLowerCase())
      .filter((name) => name.length > 3);
    if (aliases.some((name) => text.includes(name))) explicit.add(config.slug);
  }
  if (/\bstreets\b/i.test(description) && allowedMaps.has("streets-of-tarkov")) explicit.add("streets-of-tarkov");
  if (/\bground zero\b/i.test(description) && allowedMaps.has("ground-zero")) explicit.add("ground-zero");

  if (explicit.size) return [...explicit];
  const raidMaps = questMaps.filter((slug) => slug !== "anywhere");
  if (questMaps.includes("anywhere")) {
    if (isOffRaidStoryObjective(description)) return ["anywhere"];
    if (raidMaps.length) return raidMaps;
  }
  if (raidMaps.length === 1) return raidMaps;
  return questMaps;
}

function isOffRaidStoryObjective(description) {
  return /(intelligence center|off-raid|\bcraft\b|\bdecrypt\b|\bread the recovered|\bhand (?:the|it)\b|\bturn in\b)/i.test(description);
}

function questMapSlugs(quest) {
  const slugs = new Set();
  for (const name of quest.maps || []) {
    if (name === "Any Black Division location") {
      for (const location of plannerState.storyline.season_context?.black_division_locations || []) {
        slugs.add(mapSlug(location));
      }
    } else if (name === "Hideout") {
      slugs.add("anywhere");
    } else {
      slugs.add(mapSlug(name));
    }
  }
  return [...slugs].filter(Boolean);
}

function buildRegularAvailabilityContext() {
  const active = new Set(readArray(PLANNER_STORAGE.regularActive));
  const completed = new Set(readArray(PLANNER_STORAGE.regularCompleted));
  const external = readArray(PLANNER_STORAGE.external);
  const playerLevel = Number(readValue(PLANNER_STORAGE.playerLevel, 1)) || 1;
  const faction = readValue(PLANNER_STORAGE.faction, "Any");
  const reputation = readObject(PLANNER_STORAGE.reputation);
  const traders = new Map((plannerState.regular.traders || []).map((trader) => [trader.id, trader]));
  const taskById = new Map((plannerState.regular.tasks || []).map((task) => [task.id, task]));
  const groupProgress = new Map();
  for (const taskId of completed) {
    const groupId = taskById.get(taskId)?.progressionGroupId;
    if (groupId) groupProgress.set(groupId, (groupProgress.get(groupId) || 0) + 1);
  }
  return { active, completed, external, playerLevel, faction, reputation, traders, taskById, groupProgress };
}

function getRegularAvailability(task, context) {
  if (context.completed.has(task.id)) return { status: "done", reasons: [], modeledReasons: [] };
  const reasons = [];
  if (context.playerLevel < Number(task.minPlayerLevel || 0)) {
    reasons.push(`PMC level ${task.minPlayerLevel}`);
  }
  if (context.faction === "Any" && task.factionName !== "Any") {
    reasons.push(`Set PMC faction (${task.factionName} task)`);
  } else if (task.factionName !== "Any" && task.factionName !== context.faction) {
    reasons.push(`${task.factionName} only`);
  }
  if (Number(task.requiredPrestige || 0) > 0) reasons.push(`Prestige ${task.requiredPrestige}`);

  for (const requirement of task.traderRequirements || []) {
    const trader = context.traders.get(requirement.traderId);
    const actual = requirement.requirementType === "level"
      ? getPlannerLoyalty(trader, context)
      : Number(context.reputation[requirement.traderId] || 0);
    if (!comparePlannerValue(actual, requirement.compareMethod, Number(requirement.value))) {
      reasons.push(requirement.requirementType === "level"
        ? `${requirement.traderName} LL${requirement.value}`
        : `${requirement.traderName} rep ${Number(requirement.value).toFixed(2)}`);
    }
  }

  for (const requirement of task.taskRequirements || []) {
    const statuses = new Set((Array.isArray(requirement.status) ? requirement.status : [requirement.status])
      .filter(Boolean)
      .map((status) => String(status).toLowerCase()));
    const complete = context.completed.has(requirement.taskId);
    const active = context.active.has(requirement.taskId);
    if ((statuses.has("complete") && complete) || (statuses.has("active") && active)) continue;
    if (statuses.has("active") && statuses.has("complete")) {
      reasons.push(`Accept or complete ${requirement.taskName}`);
    } else if (statuses.has("active")) {
      reasons.push(`Confirm ${requirement.taskName} is active in-game`);
    } else if (statuses.has("complete")) {
      reasons.push(`Complete ${requirement.taskName}`);
    } else if (statuses.has("failed")) {
      reasons.push(`Confirm the ${requirement.taskName} branch outcome in-game`);
    } else {
      reasons.push(`Confirm the ${requirement.taskName} requirement in-game`);
    }
  }

  for (const requirement of task.globalRequirements || []) {
    const actual = context.groupProgress.get(requirement.groupId) || 0;
    if (!comparePlannerValue(actual, requirement.compareMethod, Number(requirement.value))) {
      reasons.push(`Task group ${actual}/${requirement.value}`);
    }
  }

  const modeledLoyaltyGate = progressionRules.getModeledLoyaltyGate(task);
  if (modeledLoyaltyGate) {
    const trader = context.traders.get(task.traderId);
    if (trader && getPlannerLoyalty(trader, context) < modeledLoyaltyGate.tier) {
      reasons.push(`Estimated ${task.traderName} LL${modeledLoyaltyGate.tier} ${modeledLoyaltyGate.kind}`);
    }
  }
  for (const requirement of progressionRules.getCuratedManualRequirements(task)) {
    if (!progressionRules.curatedRequirementSatisfied(requirement, context.external)) {
      reasons.push(`${requirement.label} (Wiki-only gate)`);
    }
  }
  if ((task.dialogueRequirements || []).length) reasons.push("Trader dialogue");
  if (task.hasUnresolvedRequirement) reasons.push("Special in-game condition");
  if (context.active.has(task.id)) {
    return { status: "active", reasons: [], modeledReasons: reasons };
  }
  return { status: reasons.length ? "future" : "available", reasons, modeledReasons: reasons };
}

function getPlannerLoyalty(trader, context) {
  if (!trader?.levels?.length) return 1;
  const reputation = Number(context.reputation[trader.id] || 0);
  const available = trader.levels.filter(
    (level) => context.playerLevel >= level.requiredPlayerLevel && reputation >= level.requiredReputation,
  );
  return Math.max(...available.map((level) => level.level), 1);
}

function comparePlannerValue(actual, method, expected) {
  if (method === ">=") return actual >= expected;
  if (method === ">") return actual > expected;
  if (method === "<=") return actual <= expected;
  if (method === "<") return actual < expected;
  if (method === "!=") return actual !== expected;
  return actual === expected;
}

function buildStorylineAvailabilityContext() {
  const active = new Set(readArray(PLANNER_STORAGE.storylineActive));
  const completed = new Set(readArray(PLANNER_STORAGE.storylineCompleted));
  const byName = new Map((plannerState.storyline.quests || []).map((quest) => [quest.name, quest]));
  const route = String(readValue(PLANNER_STORAGE.route, "fence")).trim().toLowerCase();
  const regularContext = buildRegularAvailabilityContext();
  return {
    active,
    completed,
    byName,
    route,
    playerLevel: regularContext.playerLevel,
    reputation: regularContext.reputation,
    traders: regularContext.traders,
  };
}

function getStorylineAvailability(quest, context) {
  if (context.completed.has(quest.id)) return { status: "done", label: "Completed", reasons: [] };
  const reasons = [];
  if (quest.available === false) reasons.push("Currently unavailable");
  if (quest.branch && quest.branch.trim().toLowerCase() !== context.route) {
    reasons.push(`${capitalizePlanner(quest.branch)} branch not selected`);
  }
  for (const requirement of quest.prerequisites || []) {
    if (!storylineRequirementSatisfied(requirement, context)) {
      reasons.push(storylineRequirementReason(requirement, context));
    }
  }
  if (quest.prerequisite_any?.length && !quest.prerequisite_any.some(
    (requirement) => storylineRequirementSatisfied(requirement, context),
  )) {
    reasons.push(quest.prerequisite_any
      .map((requirement) => storylineRequirementReason(requirement, context))
      .join(" or "));
  }
  for (const requirement of quest.requirements || []) {
    const levelMatch = requirement.match(/player level\s+(\d+)/i);
    if (levelMatch && context.playerLevel < Number(levelMatch[1])) {
      reasons.push(`PMC level ${levelMatch[1]}`);
      continue;
    }
    const loyaltyMatch = requirement.match(/^(.+?) loyalty level\s+(\d+)/i);
    if (loyaltyMatch) {
      const trader = [...context.traders.values()].find(
        (candidate) => candidate.name.toLowerCase() === loyaltyMatch[1].trim().toLowerCase(),
      );
      if (trader && getPlannerLoyalty(trader, context) < Number(loyaltyMatch[2])) {
        reasons.push(`${trader.name} LL${loyaltyMatch[2]}`);
      }
    }
  }
  if (quest.unlock_delay_hours?.length) {
    const [minimum, maximum] = quest.unlock_delay_hours;
    reasons.push(`Confirm the ${minimum}–${maximum} hour trader unlock delay has elapsed`);
  }
  if (context.active.has(quest.id)) {
    return { status: "active", label: "Active in game", reasons };
  }
  return reasons.length
    ? { status: "future", label: "Plan ahead", reasons }
    : { status: "available", label: "Storyline ready", reasons: [] };
}

function storylineRequirementSatisfied(requirement, context) {
  const prerequisite = context.byName.get(requirement.name);
  if (!prerequisite) return false;
  return requirement.status === "active"
    ? context.active.has(prerequisite.id)
    : context.completed.has(prerequisite.id);
}

function storylineRequirementReason(requirement, context) {
  const action = requirement.status === "active" ? "Accept" : "Complete";
  const note = !context.byName.has(requirement.name)
    ? " (outside KORD tracker)"
    : "";
  return `${action} ${requirement.name}${note}`;
}

function matchesPlannerFilters(row) {
  const searchBlob = [
    row.name,
    row.trader,
    row.statusLabel,
    ...row.reasons,
    ...row.objectives.map((objective) => objective.description),
    ...row.markers.map((marker) => marker.label),
  ].join(" ").toLowerCase();
  const readiness = plannerState.filters.readiness;
  const readinessMatch =
    readiness === "all" ||
    readiness === row.status ||
    (readiness === "open" && row.status !== "done");
  return (
    readinessMatch &&
    (plannerState.filters.source === "all" || plannerState.filters.source === row.source) &&
    (!plannerState.filters.search || searchBlob.includes(plannerState.filters.search))
  );
}

function comparePlannerRows(a, b) {
  if (a.key === plannerState.focusedTaskKey) return -1;
  if (b.key === plannerState.focusedTaskKey) return 1;
  const rank = { active: 0, available: 1, future: 2, done: 3 };
  return (
    rank[a.status] - rank[b.status] ||
    (a.source === "storyline" ? -1 : 1) - (b.source === "storyline" ? -1 : 1) ||
    a.trader.localeCompare(b.trader) ||
    a.name.localeCompare(b.name)
  );
}

function renderTaskPool() {
  plannerDom.objectiveList.innerHTML = plannerState.visibleRows.map(taskPoolMarkup).join("");
  plannerDom.plannerEmpty.hidden = plannerState.visibleRows.length > 0;
  plannerDom.objectiveList.hidden = plannerState.visibleRows.length === 0;
  plannerDom.poolCount.textContent = String(plannerState.visibleRows.length);
}

function taskPoolMarkup(row) {
  const planned = isRowPlanned(row);
  const exactCount = row.markers.filter((marker) => marker.confidence === "exact").length;
  const poiCount = row.markers.filter((marker) => marker.confidence === "poi").length;
  const approximateCount = row.markers.filter((marker) => marker.confidence === "approximate").length;
  const qualityClass = exactCount ? "exact" : poiCount ? "poi" : approximateCount ? "approximate" : "map-level";
  const qualityLabel = exactCount
    ? `${exactCount} exact`
    : poiCount
      ? `${poiCount} named POI`
      : approximateCount
        ? `${approximateCount} approximate`
        : "Map level";
  const open = row.key === plannerState.focusedTaskKey || plannerState.expandedTaskKeys.has(row.key);

  return `
    <article
      class="pool-task ${planned ? "is-planned" : ""} ${row.status === "active" ? "is-active-in-game" : ""} ${row.status === "done" ? "is-done" : ""} ${open ? "is-focused" : ""}"
      id="pool-${domSafe(row.key)}"
      data-pool-task="${escapePlanner(row.key)}"
      tabindex="-1"
    >
      <div class="pool-task-head">
        <div>
          <h3>${escapePlanner(row.name)}</h3>
          <div class="pool-task-meta">
            <span>${escapePlanner(row.trader)}</span>
            <span class="source-chip ${row.source}">${row.source === "storyline" ? "KORD" : "Task pool"}</span>
            <span class="readiness-chip ${row.status}">${escapePlanner(row.statusLabel)}</span>
          </div>
        </div>
        <div class="pool-task-flags">
          <span class="location-quality ${qualityClass}">${escapePlanner(qualityLabel)}</span>
        </div>
      </div>
      <details ${open ? "open" : ""}>
        <summary><span>${row.objectives.length} matching objective${row.objectives.length === 1 ? "" : "s"}</span></summary>
        <ul class="pool-objectives">
          ${row.objectives.map(objectivePoolMarkup).join("")}
        </ul>
        ${row.reasons.length ? `<ul class="pool-objectives"><li><strong>${escapePlanner(row.reasonHeading || "Not ready yet")}</strong><small>${escapePlanner(row.reasons.slice(0, 3).join(" · "))}</small></li></ul>` : ""}
        <div class="pool-task-actions">
          <button type="button" class="${planned ? "is-remove" : ""}" data-plan-toggle="${escapePlanner(row.key)}">${planned ? "Remove from raid" : "Add to raid"}</button>
          ${row.markers.length ? `<button type="button" class="is-remove" data-show-task="${escapePlanner(row.key)}">Show ${row.markers.length === 1 ? "pin" : "pins"}</button>` : ""}
          <a href="${escapePlanner(sourceTaskHref(row))}" aria-label="Open ${escapePlanner(row.name)} in its tracker">Open tracker</a>
        </div>
      </details>
    </article>
  `;
}

function objectivePoolMarkup(objective) {
  const markerCount = objective.markers.length;
  const detail = objective.quality === "exact"
    ? `${markerCount} exact game-data position${markerCount === 1 ? "" : "s"}`
    : objective.quality === "poi"
      ? `Named POI: ${[...new Set(objective.markers.map((marker) => marker.label))].join(", ")} · exact interaction point unavailable`
      : objective.quality === "approximate"
        ? `${markerCount} Wiki-guided approximate position${markerCount === 1 ? "" : "s"} · verify the field image`
        : "Map-level intelligence · no reliable coordinate";
  return `
    <li class="${objective.quality === "exact" ? "has-exact" : objective.quality === "poi" ? "has-poi" : objective.quality === "approximate" ? "has-approximate" : ""}">
      <strong>${objective.optional ? "Optional · " : ""}${escapePlanner(objective.description)}</strong>
      <small>${escapePlanner(detail)}</small>
    </li>
  `;
}

function handleTaskPoolClick(event) {
  const planButton = event.target.closest("[data-plan-toggle]");
  if (planButton) {
    toggleRowPlan(planButton.dataset.planToggle, { returnFocus: "pool" });
    return;
  }
  const showButton = event.target.closest("[data-show-task]");
  if (showButton) showTaskOnMap(showButton.dataset.showTask);
}

function handleTaskPoolToggle(event) {
  const details = event.target.closest("details");
  const task = details?.closest("[data-pool-task]");
  if (!task) return;
  if (details.open) plannerState.expandedTaskKeys.add(task.dataset.poolTask);
  else plannerState.expandedTaskKeys.delete(task.dataset.poolTask);
}

function renderMap(options = {}) {
  const config = plannerState.configBySlug.get(plannerState.selectedMap);
  const mapChanged = options.mapChanged || plannerState.renderedMap !== plannerState.selectedMap;
  const layer = selectedMapLayer(config);
  plannerDom.mapHeading.textContent = config?.name || "Unknown location";
  plannerDom.mapKicker.textContent = config?.basemapSupported
    ? config.calibrationConfidence === "approximate" ? "Approximate tactical basemap" : "Tactical basemap"
    : canProjectMap(config)
      ? "Coordinate intelligence"
      : "Location intelligence";
  plannerDom.mapSubtitle.textContent = config?.basemapSupported
    ? config.calibrationConfidence === "approximate"
      ? `${layer?.name ? `${layer.name} · ` : ""}Community artwork alignment is approximate; marker confidence stays separate.`
      : "Ground-level community SVG · exact and named-POI confidence stay separate."
    : canProjectMap(config)
      ? "World-coordinate grid · a calibrated local basemap is not available."
      : config?.unsupportedReason || "No fixed coordinates are exposed for this objective group.";

  if (mapChanged) {
    plannerState.renderedMap = plannerState.selectedMap;
    plannerState.selectedCluster = null;
    plannerState.selectedMarkerId = null;
    hideWikiPreview();
    configureMapBase(config);
  }
  renderMarkers();
}

function configureMapBase(config) {
  plannerState.artworkToken += 1;
  const token = plannerState.artworkToken;
  hydrateMapLayerControl(config);
  hydrateMapSourceLink(config);
  plannerDom.mapArtwork.hidden = true;
  plannerDom.mapArtwork.replaceChildren();
  plannerDom.mapFallbackLabel.hidden = false;
  const hasArtwork = Boolean(config?.image || config?.rasterImage);
  plannerDom.mapFallbackLabel.textContent = hasArtwork
    ? "Loading community basemap"
    : canProjectMap(config)
      ? "Coordinate grid · basemap unavailable"
    : "No fixed map coordinate";

  plannerState.mapAspect = Number(config?.artworkAspect) ||
    (canProjectMap(config) ? projectionBox(config)?.aspect || 1.5 : 1.5);
  const hasProjection = canProjectMap(config);
  plannerDom.mapZoomIn.disabled = !hasProjection;
  plannerDom.mapZoomOut.disabled = !hasProjection;
  plannerDom.mapReset.disabled = !hasProjection;
  applyMapGeometry();

  if (hasArtwork) {
    loadMapArtwork(config, token);
  }

  window.requestAnimationFrame(() => resetMapView({ keepZoom: true }));
}

async function loadMapArtwork(config, token) {
  const layer = selectedMapLayer(config);
  if (config.rasterImage) {
    loadRasterArtwork(config, token);
    return;
  }
  try {
    const response = await fetch(config.image);
    if (!response.ok) throw new Error(`${config.image} returned ${response.status}`);
    const source = await response.text();
    if (token !== plannerState.artworkToken) return;
    const parsed = new DOMParser().parseFromString(source, "image/svg+xml");
    const svg = parsed.documentElement;
    if (svg.nodeName.toLowerCase() !== "svg" || parsed.querySelector("parsererror")) {
      throw new Error("Invalid SVG basemap");
    }

    for (const unsafe of svg.querySelectorAll("script, foreignObject, iframe, object, embed")) unsafe.remove();
    for (const element of svg.querySelectorAll("*")) {
      for (const attribute of [...element.attributes]) {
        if (/^on/i.test(attribute.name)) element.removeAttribute(attribute.name);
      }
    }
    const svgLayer = layer?.svgLayer || config.svgLayer;
    for (const group of [...svg.children].filter((child) => child.nodeName.toLowerCase() === "g")) {
      const keep = !group.id ||
        group.id === svgLayer ||
        group.getAttribute("data-keep-with-group") === svgLayer;
      if (!keep) group.setAttribute("display", "none");
    }
    if (config.stretchArtwork) svg.setAttribute("preserveAspectRatio", "none");
    svg.removeAttribute("width");
    svg.removeAttribute("height");
    plannerDom.mapArtwork.replaceChildren(document.importNode(svg, true));
    plannerDom.mapArtwork.hidden = false;
    plannerDom.mapFallbackLabel.hidden = true;
  } catch (error) {
    if (token !== plannerState.artworkToken) return;
    plannerDom.mapArtwork.hidden = true;
    plannerDom.mapFallbackLabel.hidden = false;
    plannerDom.mapFallbackLabel.textContent = "Basemap failed · coordinate grid active";
    console.error(error);
  }
}

function loadRasterArtwork(config, token) {
  const image = document.createElement("img");
  image.className = "map-raster";
  image.alt = "";
  image.decoding = "async";
  image.referrerPolicy = "no-referrer";
  image.addEventListener("load", () => {
    if (token !== plannerState.artworkToken) return;
    plannerDom.mapArtwork.replaceChildren(image);
    plannerDom.mapArtwork.hidden = false;
    plannerDom.mapFallbackLabel.hidden = true;
  });
  image.addEventListener("error", () => {
    if (token !== plannerState.artworkToken) return;
    plannerDom.mapArtwork.hidden = true;
    plannerDom.mapFallbackLabel.hidden = false;
    plannerDom.mapFallbackLabel.textContent = "Online basemap unavailable · coordinate grid active";
  });
  image.src = config.rasterImage;
}

function mapLayers(config) {
  if (config?.rasterImage) return [];
  return Array.isArray(config?.layers) ? config.layers : [];
}

function selectedMapLayer(config) {
  const layers = mapLayers(config);
  if (!layers.length) return null;
  const selectedId = plannerState.mapLayerBySlug.get(config.slug) || config.defaultLayer || layers[0].id;
  const selected = layers.find((layer) => layer.id === selectedId) || layers[0];
  plannerState.mapLayerBySlug.set(config.slug, selected.id);
  return selected;
}

function hydrateMapLayerControl(config) {
  const layers = mapLayers(config);
  plannerDom.mapLayerControl.hidden = layers.length < 2;
  plannerDom.mapLayer.disabled = layers.length < 2;
  if (layers.length < 2) {
    plannerDom.mapLayer.replaceChildren();
    return;
  }
  const selected = selectedMapLayer(config);
  plannerDom.mapLayer.innerHTML = layers
    .map((layer) => `<option value="${escapePlanner(layer.id)}">${escapePlanner(layer.name)}</option>`)
    .join("");
  plannerDom.mapLayer.value = selected.id;
}

function hydrateMapSourceLink(config) {
  const visible = Boolean(config?.sourceUrl);
  plannerDom.mapSourceLink.hidden = !visible;
  if (!visible) return;
  plannerDom.mapSourceLink.href = config.sourceUrl;
  plannerDom.mapSourceLink.textContent = `${config.sourceLabel || "Open map source"} ↗`;
}

function renderMarkers() {
  const config = plannerState.configBySlug.get(plannerState.selectedMap);
  const markerRows = markerRowsForCurrentFilter();
  const markers = markerRows.flatMap((row) => row.markers);
  const projected = canProjectMap(config)
    ? markers.map((marker) => ({
        marker,
        point: projectPosition(config, marker.position),
        offLevel: markerIsOffSelectedLayer(config, marker),
      }))
        .filter((entry) => entry.point && entry.point.left >= -0.02 && entry.point.left <= 1.02 && entry.point.top >= -0.02 && entry.point.top <= 1.02)
    : [];

  hideWikiPreview();
  plannerState.clusters = clusterMarkers(projected);
  plannerState.selectedCluster = plannerState.selectedMarkerId
    ? plannerState.clusters.findIndex((cluster) =>
        cluster.entries.some((entry) => entry.marker.id === plannerState.selectedMarkerId))
    : -1;
  if (plannerState.selectedCluster < 0) {
    plannerState.selectedCluster = null;
    plannerState.selectedMarkerId = null;
  }
  plannerDom.markerLayer.innerHTML = plannerState.clusters.map((cluster, index) => {
    const taskNames = [...new Set(cluster.entries.map((entry) => entry.marker.taskName))];
    const confidences = new Set(cluster.entries.map((entry) => entry.marker.confidence));
    const confidence = confidences.size === 1 ? [...confidences][0] : "exact";
    const offLevel = cluster.entries.every((entry) => entry.offLevel);
    const count = cluster.entries.length;
    const confidenceLabel = confidence === "poi"
      ? "named POI"
      : confidence === "approximate"
        ? "Wiki-guided approximation"
        : confidences.size > 1 ? "mixed confidence" : "exact game-data";
    const label = count > 1
      ? `${count} quest objective markers, ${confidenceLabel}: ${taskNames.join(", ")}`
      : `${confidenceLabel} marker, ${taskNames[0]}: ${cluster.entries[0].marker.description}`;
    const selected = plannerState.selectedCluster === index;
    return `
      <button
        class="map-marker ${confidence} ${offLevel ? "is-off-level" : ""} ${count > 1 ? "is-cluster" : ""} ${selected ? "is-selected" : ""}"
        type="button"
        style="left:${(cluster.left * 100).toFixed(3)}%;top:${(cluster.top * 100).toFixed(3)}%"
        data-cluster-index="${index}"
        aria-label="${escapePlanner(`${label}${offLevel ? "; shown over another map level" : ""}`)}"
        aria-controls="wiki-hover-preview"
        aria-expanded="false"
        aria-pressed="${String(selected)}"
      ><span>${count > 1 ? count : ""}</span></button>
    `;
  }).join("");

  renderMarkerDetail(plannerState.selectedCluster === null
    ? null
    : plannerState.clusters[plannerState.selectedCluster]);
}

function markerRowsForCurrentFilter() {
  return plannerState.filters.pinMode === "planned"
    ? plannerState.visibleRows.filter(isRowPlanned)
    : plannerState.visibleRows;
}

function canProjectMap(config) {
  return Boolean(config?.bounds && config.calibrationSupported !== false);
}

function layerForMarker(config, marker) {
  if (marker.floorLabel) return null;
  if (!Number.isFinite(marker.position?.y)) return null;
  const y = Number(marker.position.y);
  return mapLayers(config).find((layer) => {
    if (!Array.isArray(layer.heightRange)) return false;
    const minimum = Number(layer.heightRange[0]);
    const maximum = Number(layer.heightRange[1]);
    return y >= minimum && y < maximum;
  }) || null;
}

function markerIsOffSelectedLayer(config, marker) {
  const markerLayer = layerForMarker(config, marker);
  const selectedLayer = selectedMapLayer(config);
  return Boolean(markerLayer && selectedLayer && markerLayer.id !== selectedLayer.id);
}

function clusterMarkers(projected) {
  const groups = new Map();
  const divisions = Math.max(32, Math.round(32 * plannerState.zoom));
  for (const entry of projected) {
    const cellX = Math.round(entry.point.left * divisions);
    const cellY = Math.round(entry.point.top * divisions);
    const key = `${cellX}:${cellY}`;
    const cluster = groups.get(key) || { entries: [], left: 0, top: 0 };
    cluster.entries.push(entry);
    cluster.left += entry.point.left;
    cluster.top += entry.point.top;
    groups.set(key, cluster);
  }
  return [...groups.values()].map((cluster) => ({
    ...cluster,
    left: cluster.left / cluster.entries.length,
    top: cluster.top / cluster.entries.length,
  }));
}

function selectCluster(index, options = {}) {
  const cluster = plannerState.clusters[index];
  if (!cluster) return;
  plannerState.selectedCluster = index;
  plannerState.selectedMarkerId = cluster.entries[0]?.marker.id || null;
  for (const marker of plannerDom.markerLayer.querySelectorAll("[data-cluster-index]")) {
    const selected = Number(marker.dataset.clusterIndex) === index;
    marker.classList.toggle("is-selected", selected);
    marker.setAttribute("aria-pressed", String(selected));
  }
  renderMarkerDetail(cluster);
  if (options.center) centerMapPoint(cluster.left, cluster.top);
}

function renderMarkerDetail(cluster) {
  if (!cluster) {
    plannerDom.markerDetail.innerHTML =
      '<p class="eyebrow">Selected position</p><p>Select a marker to inspect the quests sharing that position. Hover or focus a marker to load available Wiki field images.</p>';
    return;
  }
  const unique = new Map();
  for (const entry of cluster.entries) {
    const marker = entry.marker;
    const key = `${marker.rowKey}:${marker.objectiveIndex}`;
    const group = unique.get(key) || { marker, count: 0 };
    group.count += 1;
    unique.set(key, group);
  }
  plannerDom.markerDetail.innerHTML = `
    <p class="eyebrow">Selected position / ${cluster.entries.length} marker${cluster.entries.length === 1 ? "" : "s"}</p>
    <div class="marker-detail-list">
      ${[...unique.values()].map(({ marker, count }) => {
        const row = plannerState.rows.find((item) => item.key === marker.rowKey);
        const planned = row ? isRowPlanned(row) : false;
        return `
          <article class="marker-entry">
            <h3>${escapePlanner(marker.taskName)}</h3>
            <div class="marker-entry-meta">
              <span class="location-quality ${marker.confidence}">${marker.confidence === "exact" ? "Exact" : marker.confidence === "approximate" ? "Approximate" : "Named POI"}</span>
              ${floorMarkup(marker)}
            </div>
            <p><strong>${escapePlanner(marker.label)}</strong> · ${escapePlanner(marker.description)}</p>
            <p>${escapePlanner(marker.detail)}${count > 1 ? ` ${count} nearby positions are grouped at this zoom.` : ""}</p>
            <div class="marker-entry-actions">
              <button type="button" class="${planned ? "is-remove" : ""}" data-marker-plan="${escapePlanner(marker.rowKey)}">${planned ? "Remove from raid" : "Add to raid"}</button>
              <a href="${escapePlanner(row ? sourceTaskHref(row) : "#")}" aria-label="Open ${escapePlanner(marker.taskName)} in its tracker">Open tracker</a>
            </div>
          </article>
        `;
      }).join("")}
    </div>
  `;
}

function floorMarkup(marker) {
  if (marker.floorLabel) return `<span class="floor-chip">${escapePlanner(marker.floorLabel)}</span>`;
  if (!Number.isFinite(marker.position?.y)) return "";
  const layer = layerForMarker(plannerState.configBySlug.get(plannerState.selectedMap), marker);
  const elevation = marker.position.y.toFixed(1);
  return `<span class="floor-chip">${layer ? `${escapePlanner(layer.name)} · ` : ""}Elevation ${escapePlanner(elevation)}</span>`;
}

function handleMarkerDetailClick(event) {
  const button = event.target.closest("[data-marker-plan]");
  if (button) toggleRowPlan(button.dataset.markerPlan, { returnFocus: "detail" });
}

function renderRaidPlan() {
  const currentPlan = currentRaidEntries();
  const map = plannerState.configBySlug.get(plannerState.selectedMap);
  const mapName = map?.name || "Current location";
  plannerDom.raidPlanHeading.textContent = `${mapName} raid`;
  plannerDom.raidPlanIntro.textContent = `Order the route for ${mapName}. Completion still belongs to the source tracker.`;
  plannerDom.raidPlanList.innerHTML = currentPlan.map(({ entry }, index) => {
    const objectives = raidPlanObjectives(entry);
    return `
      <li class="raid-plan-item" data-plan-item="${escapePlanner(planEntryKey(entry))}">
        <div class="raid-plan-copy">
          <strong>${escapePlanner(entry.name)}</strong>
          <small>${escapePlanner(entry.trader || (entry.source === "storyline" ? "KORD storyline" : "Task pool"))}</small>
          ${objectives.length ? `
            <details class="raid-plan-objectives">
              <summary>${objectives.length} objective${objectives.length === 1 ? "" : "s"} on ${escapePlanner(mapName)}</summary>
              <ul>${objectives.map((objective) => `<li>${escapePlanner(objective)}</li>`).join("")}</ul>
            </details>
          ` : ""}
        </div>
        <div class="raid-plan-controls">
          <button type="button" data-plan-move="-1" aria-label="Move ${escapePlanner(entry.name)} earlier" ${index === 0 ? "disabled" : ""}>↑</button>
          <button type="button" data-plan-move="1" aria-label="Move ${escapePlanner(entry.name)} later" ${index === currentPlan.length - 1 ? "disabled" : ""}>↓</button>
          <button type="button" data-plan-remove aria-label="Remove ${escapePlanner(entry.name)} from raid">Remove</button>
        </div>
      </li>
    `;
  }).join("");
  plannerDom.raidPlanEmpty.hidden = currentPlan.length > 0;
  plannerDom.clearRaidPlan.disabled = currentPlan.length === 0;
  plannerDom.raidPlanTotal.textContent = String(currentPlan.length);
}

function currentRaidEntries() {
  return plannerState.plan
    .map((entry, globalIndex) => ({ entry, globalIndex }))
    .filter(({ entry }) => entry.mapSlug === plannerState.selectedMap);
}

function raidPlanObjectives(entry) {
  const row = plannerState.rows.find((candidate) =>
    candidate.source === entry.source && candidate.taskId === entry.taskId && candidate.mapSlug === entry.mapSlug);
  return row ? row.objectives.map((objective) => objective.description) : [];
}

function handleRaidPlanClick(event) {
  const item = event.target.closest("[data-plan-item]");
  if (!item) return;
  const currentPlan = currentRaidEntries();
  const localIndex = currentPlan.findIndex(({ entry }) => planEntryKey(entry) === item.dataset.planItem);
  if (localIndex < 0) return;
  const { globalIndex } = currentPlan[localIndex];
  if (event.target.closest("[data-plan-remove]")) {
    const nextEntry = currentPlan[localIndex + 1]?.entry || currentPlan[localIndex - 1]?.entry || null;
    const [removed] = plannerState.plan.splice(globalIndex, 1);
    persistPlan();
    renderPlanner();
    showPlannerToast(`${removed.name} removed from the raid.`);
    window.requestAnimationFrame(() => {
      if (nextEntry) {
        plannerDom.raidPlanList
          .querySelector(`[data-plan-item="${cssEscape(planEntryKey(nextEntry))}"] [data-plan-remove]`)
          ?.focus();
      } else {
        plannerDom.raidPlanHeading.tabIndex = -1;
        plannerDom.raidPlanHeading.focus();
      }
    });
    return;
  }
  const move = event.target.closest("[data-plan-move]");
  if (!move) return;
  const direction = Number(move.dataset.planMove);
  const targetLocalIndex = localIndex + direction;
  if (targetLocalIndex < 0 || targetLocalIndex >= currentPlan.length) return;
  const targetGlobalIndex = currentPlan[targetLocalIndex].globalIndex;
  [plannerState.plan[globalIndex], plannerState.plan[targetGlobalIndex]] = [
    plannerState.plan[targetGlobalIndex],
    plannerState.plan[globalIndex],
  ];
  persistPlan();
  renderPlanner();
  window.requestAnimationFrame(() => {
    const movedItem = plannerDom.raidPlanList.querySelector(
      `[data-plan-item="${cssEscape(planEntryKey(currentPlan[localIndex].entry))}"]`,
    );
    movedItem?.querySelector(
      `[data-plan-move="${escapePlanner(move.dataset.planMove)}"]:not(:disabled), [data-plan-move]:not(:disabled), [data-plan-remove]`,
    )?.focus();
  });
}

function toggleRowPlan(rowKey, options = {}) {
  const row = plannerState.rows.find((item) => item.key === rowKey);
  if (!row) return;
  const key = rowPlanKey(row);
  const index = plannerState.plan.findIndex((entry) => planEntryKey(entry) === key);
  let message;
  if (index >= 0) {
    plannerState.plan.splice(index, 1);
    message = `${row.name} removed from the raid.`;
  } else {
    plannerState.plan.push({
      source: row.source,
      taskId: row.taskId,
      mapSlug: row.mapSlug,
      name: row.name,
      trader: row.trader,
    });
    message = `${row.name} added to the raid.`;
  }
  persistPlan();
  renderPlanner();
  showPlannerToast(message);
  window.requestAnimationFrame(() => {
    const selector = options.returnFocus === "detail" ? "[data-marker-plan]" : "[data-plan-toggle]";
    [...document.querySelectorAll(selector)].find((button) =>
      (button.dataset.markerPlan || button.dataset.planToggle) === rowKey)?.focus();
  });
}

function isRowPlanned(row) {
  const key = rowPlanKey(row);
  return plannerState.plan.some((entry) => planEntryKey(entry) === key);
}

function rowPlanKey(row) {
  return `${row.source}:${row.taskId}:${row.mapSlug}`;
}

function planEntryKey(entry) {
  return `${entry.source}:${entry.taskId}:${entry.mapSlug}`;
}

function validateStoredPlan() {
  const seen = new Set();
  const rowsByMap = new Map();
  const validated = [];
  for (const entry of plannerState.plan) {
    if (!entry || typeof entry.taskId !== "string" ||
      typeof entry.mapSlug !== "string" || !plannerState.configBySlug.has(entry.mapSlug)) continue;
    if (!rowsByMap.has(entry.mapSlug)) {
      rowsByMap.set(entry.mapSlug, [
        ...buildStorylineRows(entry.mapSlug),
        ...buildRegularRows(entry.mapSlug),
      ]);
    }
    const row = rowsByMap.get(entry.mapSlug).find((candidate) =>
      candidate.source === entry.source && candidate.taskId === entry.taskId);
    if (!row) continue;
    const key = planEntryKey(entry);
    if (seen.has(key)) continue;
    seen.add(key);
    validated.push({
      source: row.source,
      taskId: row.taskId,
      mapSlug: row.mapSlug,
      name: row.name,
      trader: row.trader,
    });
  }
  plannerState.plan = validated;
  persistPlan();
}

function persistPlan() {
  writeValue(PLANNER_STORAGE.plan, JSON.stringify(plannerState.plan));
}

function updatePlannerSummary() {
  const markerRows = markerRowsForCurrentFilter();
  const visibleMarkers = markerRows.flatMap((row) => row.markers);
  const exactCount = distinctMarkerLocationCount(visibleMarkers, "exact");
  const poiCount = distinctMarkerLocationCount(visibleMarkers, "poi");
  const approximateCount = distinctMarkerLocationCount(visibleMarkers, "approximate");
  const mapLevel = markerRows.reduce(
    (total, row) => total + row.objectives.filter((objective) => !objective.markers.length).length,
    0,
  );
  plannerDom.visibleTaskTotal.textContent = String(plannerState.visibleRows.length);
  plannerDom.exactPinTotal.textContent = String(exactCount);
  plannerDom.poolCount.textContent = String(plannerState.visibleRows.length);
  const questSummary = plannerState.filters.pinMode === "planned"
    ? `${markerRows.length} planned quest${markerRows.length === 1 ? "" : "s"} mapped · ${plannerState.visibleRows.length} in the pool`
    : `${plannerState.visibleRows.length} quest${plannerState.visibleRows.length === 1 ? "" : "s"}`;
  plannerDom.plannerStatus.textContent =
    `${questSummary} · ${exactCount} distinct exact location${exactCount === 1 ? "" : "s"} · ${poiCount} named POI${poiCount === 1 ? "" : "s"} · ${approximateCount} approximate pin${approximateCount === 1 ? "" : "s"} · ${mapLevel} map-level objective${mapLevel === 1 ? "" : "s"}.`;
}

function distinctMarkerLocationCount(markers, confidence) {
  return new Set(markers
    .filter((marker) => marker.confidence === confidence)
    .map((marker) => marker.position.left !== undefined
      ? [marker.position.left, marker.position.top].join(":")
      : [marker.position.x, marker.position.y ?? "", marker.position.z].join(":")))
    .size;
}

function showTaskOnMap(rowKey) {
  const config = plannerState.configBySlug.get(plannerState.selectedMap);
  const row = plannerState.visibleRows.find((item) => item.key === rowKey);
  const markerLayer = row?.markers.map((marker) => layerForMarker(config, marker)).find(Boolean);
  const selectedLayer = selectedMapLayer(config);
  if (markerLayer && selectedLayer && markerLayer.id !== selectedLayer.id) {
    plannerState.mapLayerBySlug.set(config.slug, markerLayer.id);
    plannerState.renderedMap = null;
    renderPlanner({ mapChanged: true });
    window.requestAnimationFrame(() => showTaskOnMap(rowKey));
    return;
  }
  const clusterIndex = plannerState.clusters.findIndex(
    (cluster) => cluster.entries.some((entry) => entry.marker.rowKey === rowKey),
  );
  if (clusterIndex < 0) {
    showPlannerToast("This quest has no visible marker under the current marker filter.");
    return;
  }
  selectCluster(clusterIndex, { center: true });
  queueWikiPreview(clusterIndex, 0);
  plannerDom.markerLayer.querySelector(`[data-cluster-index="${clusterIndex}"]`)?.focus({ preventScroll: true });
}

function projectionBox(config) {
  if (!config?.bounds?.length) return null;
  const xMin = Math.min(config.bounds[0][0], config.bounds[1][0]);
  const xMax = Math.max(config.bounds[0][0], config.bounds[1][0]);
  const zMin = Math.min(config.bounds[0][1], config.bounds[1][1]);
  const zMax = Math.max(config.bounds[0][1], config.bounds[1][1]);
  const northWest = transformWorld(config, xMin, zMax);
  const southEast = transformWorld(config, xMax, zMin);
  const left = Math.min(northWest.x, southEast.x);
  const right = Math.max(northWest.x, southEast.x);
  const top = Math.min(northWest.y, southEast.y);
  const bottom = Math.max(northWest.y, southEast.y);
  const width = Math.max(right - left, 0.0001);
  const height = Math.max(bottom - top, 0.0001);
  return { left, right, top, bottom, width, height, aspect: width / height };
}

function transformWorld(config, x, z) {
  const radians = (Number(config.coordinateRotation || 0) * Math.PI) / 180;
  const rotatedX = x * Math.cos(radians) - z * Math.sin(radians);
  const rotatedZ = x * Math.sin(radians) + z * Math.cos(radians);
  const transform = config.crsSimpleTransformation || [1, 0, 1, 0];
  return {
    x: transform[0] * rotatedX + transform[1],
    y: -transform[2] * rotatedZ + transform[3],
  };
}

function projectPosition(config, position) {
  if (position && position.left !== null && position.left !== undefined &&
    position.top !== null && position.top !== undefined &&
    Number.isFinite(Number(position.left)) && Number.isFinite(Number(position.top))) {
    return { left: Number(position.left), top: Number(position.top) };
  }
  if (!hasFinitePosition(position)) return null;
  const box = projectionBox(config);
  if (!box) return null;
  const point = transformWorld(config, Number(position.x), Number(position.z));
  const left = (point.x - box.left) / box.width;
  const top = (point.y - box.top) / box.height;
  const insets = config.projectionInsets || {};
  const insetLeft = Number(insets.left || 0);
  const insetRight = Number(insets.right || 0);
  const insetTop = Number(insets.top || 0);
  const insetBottom = Number(insets.bottom || 0);
  return {
    left: insetLeft + left * (1 - insetLeft - insetRight),
    top: insetTop + top * (1 - insetTop - insetBottom),
  };
}

function applyMapGeometry(options = {}) {
  const viewport = plannerDom.mapViewport;
  if (!viewport) return;
  const oldCenterX = viewport.scrollWidth ? (viewport.scrollLeft + viewport.clientWidth / 2) / viewport.scrollWidth : 0.5;
  const oldCenterY = viewport.scrollHeight ? (viewport.scrollTop + viewport.clientHeight / 2) / viewport.scrollHeight : 0.5;
  const minimum = window.innerWidth <= 580 ? 650 : 720;
  const baseWidth = Math.max(viewport.clientWidth, minimum);
  const baseHeight = Math.round(baseWidth / Math.max(plannerState.mapAspect, 0.2));
  const minimumViewportHeight = window.innerWidth <= 580 ? 500 : 470;
  viewport.style.height = `${Math.min(780, Math.max(minimumViewportHeight, baseHeight))}px`;
  const width = Math.round(baseWidth * plannerState.zoom);
  const height = Math.max(260, Math.round(width / Math.max(plannerState.mapAspect, 0.2)));
  plannerDom.mapStage.style.width = `${width}px`;
  plannerDom.mapStage.style.minWidth = "0";
  plannerDom.mapStage.style.minHeight = "0";
  plannerDom.mapStage.style.height = `${height}px`;
  plannerDom.mapZoomLevel.value = `${Math.round(plannerState.zoom * 100)}%`;
  plannerDom.mapZoomLevel.textContent = `${Math.round(plannerState.zoom * 100)}%`;
  const projectionAvailable = canProjectMap(plannerState.configBySlug.get(plannerState.selectedMap));
  plannerDom.mapZoomOut.disabled = !projectionAvailable || plannerState.zoom <= 0.75;
  plannerDom.mapZoomIn.disabled = !projectionAvailable || plannerState.zoom >= 3;
  if (options.preserveCenter) {
    window.requestAnimationFrame(() => {
      viewport.scrollLeft = oldCenterX * viewport.scrollWidth - viewport.clientWidth / 2;
      viewport.scrollTop = oldCenterY * viewport.scrollHeight - viewport.clientHeight / 2;
    });
  }
}

function setMapZoom(value) {
  const oldZoom = plannerState.zoom;
  plannerState.zoom = Math.min(3, Math.max(0.75, Math.round(value * 4) / 4));
  if (oldZoom === plannerState.zoom) return;
  applyMapGeometry({ preserveCenter: true });
  renderMarkers();
}

function resetMapView(options = {}) {
  const oldZoom = plannerState.zoom;
  if (!options.keepZoom) plannerState.zoom = 1;
  applyMapGeometry();
  if (oldZoom !== plannerState.zoom) renderMarkers();
  window.requestAnimationFrame(() => {
    plannerDom.mapViewport.scrollLeft = Math.max(0, (plannerDom.mapViewport.scrollWidth - plannerDom.mapViewport.clientWidth) / 2);
    plannerDom.mapViewport.scrollTop = Math.max(0, (plannerDom.mapViewport.scrollHeight - plannerDom.mapViewport.clientHeight) / 2);
  });
}

function centerMapPoint(left, top) {
  const viewport = plannerDom.mapViewport;
  const behavior = window.matchMedia("(prefers-reduced-motion: reduce)").matches ? "auto" : "smooth";
  viewport.scrollTo({
    left: left * viewport.scrollWidth - viewport.clientWidth / 2,
    top: top * viewport.scrollHeight - viewport.clientHeight / 2,
    behavior,
  });
}

function handleMapKeyboard(event) {
  if (event.target !== plannerDom.mapViewport) return;
  const step = event.shiftKey ? 140 : 52;
  const movements = {
    ArrowLeft: [-step, 0],
    ArrowRight: [step, 0],
    ArrowUp: [0, -step],
    ArrowDown: [0, step],
  };
  if (movements[event.key]) {
    event.preventDefault();
    plannerDom.mapViewport.scrollBy(...movements[event.key]);
  } else if (event.key === "+" || event.key === "=") {
    event.preventDefault();
    setMapZoom(plannerState.zoom + 0.25);
  } else if (event.key === "-") {
    event.preventDefault();
    setMapZoom(plannerState.zoom - 0.25);
  } else if (event.key === "0") {
    event.preventDefault();
    resetMapView();
  }
}

function beginMapDrag(event) {
  if (event.button !== 0 || event.target.closest("button, a")) return;
  mapDrag = {
    pointerId: event.pointerId,
    x: event.clientX,
    y: event.clientY,
    left: plannerDom.mapViewport.scrollLeft,
    top: plannerDom.mapViewport.scrollTop,
  };
  plannerDom.mapViewport.setPointerCapture(event.pointerId);
  plannerDom.mapViewport.classList.add("is-dragging");
}

function continueMapDrag(event) {
  if (!mapDrag || mapDrag.pointerId !== event.pointerId) return;
  plannerDom.mapViewport.scrollLeft = mapDrag.left - (event.clientX - mapDrag.x);
  plannerDom.mapViewport.scrollTop = mapDrag.top - (event.clientY - mapDrag.y);
}

function endMapDrag(event) {
  if (!mapDrag || mapDrag.pointerId !== event.pointerId) return;
  mapDrag = null;
  plannerDom.mapViewport.classList.remove("is-dragging");
}

function handleMarkerPointerOver(event) {
  const marker = event.target.closest("[data-cluster-index]");
  if (!marker || marker.contains(event.relatedTarget)) return;
  queueWikiPreview(Number(marker.dataset.clusterIndex), 220, { trigger: marker });
}

function handleMarkerPointerOut(event) {
  const marker = event.target.closest("[data-cluster-index]");
  if (!marker || marker.contains(event.relatedTarget)) return;
  scheduleWikiHide();
}

function queueWikiPreview(clusterIndex, delay, options = {}) {
  window.clearTimeout(wikiHoverTimer);
  cancelWikiHide();
  wikiHoverTimer = window.setTimeout(() => showWikiPreview(clusterIndex, options), delay);
}

async function showWikiPreview(clusterIndex, options = {}) {
  const cluster = plannerState.clusters[clusterIndex];
  if (!cluster) return;
  const marker = cluster.entries.map((entry) => entry.marker).find((entry) => entry.wikiLink);
  if (!marker) {
    hideWikiPreview();
    return;
  }
  if (activeWikiTrigger && activeWikiTrigger !== options.trigger) {
    activeWikiTrigger.setAttribute("aria-expanded", "false");
  }
  activeWikiTrigger = options.trigger || activeWikiTrigger;
  activeWikiTrigger?.setAttribute("aria-expanded", "true");
  const token = ++wikiRequestToken;
  plannerDom.wikiPreviewTitle.textContent = marker.taskName;
  plannerDom.wikiPreviewBody.className = "wiki-preview-body is-loading";
  plannerDom.wikiPreviewBody.textContent = "Loading available field images from the Wiki…";
  plannerDom.wikiHoverPreview.hidden = false;
  if (options.focusPreview) {
    window.requestAnimationFrame(() => plannerDom.closeWikiPreview.focus());
  }

  try {
    const row = plannerState.rows.find((item) => item.key === marker.rowKey);
    const objectiveTexts = row?.objectives.map((objective) => objective.description) || [marker.description];
    const images = await loadWikiImages(
      marker.wikiLink,
      plannerState.selectedMap,
      marker.taskName,
      objectiveTexts,
      wikiTaskSpansMultipleMaps(marker),
    );
    if (token !== wikiRequestToken) return;
    if (!images.length) {
      plannerDom.wikiPreviewBody.className = "wiki-preview-body is-empty";
      plannerDom.wikiPreviewBody.innerHTML =
        `No location screenshot is indexed for this quest. <a href="${escapePlanner(marker.wikiLink)}" target="_blank" rel="noreferrer">Open the Wiki page ↗</a>`;
      return;
    }
    plannerDom.wikiPreviewBody.className = "wiki-preview-body";
    plannerDom.wikiPreviewBody.innerHTML = `
      ${images.map((image) => `
        <a class="wiki-preview-image" href="${escapePlanner(image.descriptionUrl || marker.wikiLink)}" target="_blank" rel="noreferrer">
          <img src="${escapePlanner(image.thumbnailUrl)}" alt="${escapePlanner(cleanImageName(image.title))}" loading="eager">
          <span><strong>${escapePlanner(cleanImageName(image.title))}</strong><small>${escapePlanner(image.rights)}</small></span>
        </a>
      `).join("")}
      <p class="wiki-preview-credit">Externally hosted Wiki images. Each thumbnail links to its file page for full author and rights details. <a href="${escapePlanner(marker.wikiLink)}" target="_blank" rel="noreferrer">Open quest page ↗</a></p>
    `;
  } catch (error) {
    if (token !== wikiRequestToken) return;
    plannerDom.wikiPreviewBody.className = "wiki-preview-body is-empty";
    plannerDom.wikiPreviewBody.innerHTML =
      `Preview unavailable. <a href="${escapePlanner(marker.wikiLink)}" target="_blank" rel="noreferrer">Open the Wiki page ↗</a>`;
    console.debug("Wiki preview unavailable", error);
  }
}

async function loadWikiImages(wikiLink, selectedMap, taskName, objectiveTexts, spansMultipleMaps) {
  const cacheKey = `${wikiLink}|${selectedMap}`;
  if (wikiPreviewCache.has(cacheKey)) return wikiPreviewCache.get(cacheKey);
  const promise = fetchWikiImages(
    wikiLink,
    selectedMap,
    taskName,
    objectiveTexts,
    spansMultipleMaps,
  ).catch((error) => {
    wikiPreviewCache.delete(cacheKey);
    throw error;
  });
  wikiPreviewCache.set(cacheKey, promise);
  return promise;
}

async function fetchWikiImages(wikiLink, selectedMap, taskName, objectiveTexts, spansMultipleMaps) {
  const pageUrl = new URL(wikiLink);
  const marker = "/wiki/";
  const wikiIndex = pageUrl.pathname.indexOf(marker);
  if (wikiIndex < 0) return [];
  const pageTitle = decodeURIComponent(pageUrl.pathname.slice(wikiIndex + marker.length));
  const api = `${pageUrl.origin}/api.php`;
  const parseUrl = new URL(api);
  parseUrl.search = new URLSearchParams({
    action: "parse",
    page: pageTitle,
    prop: "images",
    format: "json",
    origin: "*",
  });
  const parseResponse = await fetch(parseUrl);
  if (!parseResponse.ok) throw new Error(`Wiki image index returned ${parseResponse.status}`);
  const parsed = await parseResponse.json();
  const scoredImages = (parsed.parse?.images || [])
    .map((title) => ({
      title,
      score: scoreWikiImage(title, selectedMap, taskName, objectiveTexts),
    }))
    .filter((entry) => Number.isFinite(entry.score))
    .filter((entry) =>
      !spansMultipleMaps ||
      wikiImageMatchesMap(entry.title, selectedMap) ||
      wikiImageMatchesObjectives(entry.title, objectiveTexts))
    .sort((a, b) => b.score - a.score || a.title.localeCompare(b.title));
  const filenames = scoredImages
    .slice(0, 4)
    .map((entry) => entry.title);
  if (!filenames.length) return [];

  const imageUrl = new URL(api);
  imageUrl.search = new URLSearchParams({
    action: "query",
    titles: filenames.map((title) => `File:${title}`).join("|"),
    prop: "imageinfo",
    iiprop: "url|extmetadata",
    iiurlwidth: "520",
    format: "json",
    origin: "*",
  });
  const imageResponse = await fetch(imageUrl);
  if (!imageResponse.ok) throw new Error(`Wiki thumbnails returned ${imageResponse.status}`);
  const imageData = await imageResponse.json();
  return Object.values(imageData.query?.pages || {})
    .map((page) => {
      const info = page.imageinfo?.[0];
      return info ? {
        title: page.title?.replace(/^File:/, "") || "Wiki location image",
        thumbnailUrl: info.thumburl || info.url,
        descriptionUrl: info.descriptionurl || wikiLink,
        rights: wikiImageRights(info.extmetadata),
      } : null;
    })
    .filter(Boolean);
}

function scoreWikiImage(filename, selectedMap, taskName, objectiveTexts = []) {
  const lower = filename.toLowerCase();
  if (!/\.(png|jpe?g|webp)$/i.test(filename)) return Number.NEGATIVE_INFINITY;
  if (/(^|[_\s-])(icon|banner|logo|portrait|trader|achievement|item)([_\s.-]|$)/i.test(filename)) {
    return Number.NEGATIVE_INFINITY;
  }
  const compact = looseSlug(filename);
  const taskCompact = looseSlug(taskName);
  const config = plannerState.configBySlug.get(selectedMap);
  const mapTerms = [config?.name, ...(config?.aliases || [])]
    .filter(Boolean)
    .map(looseSlug);
  let score = 0;
  if (compact.includes(taskCompact)) score += 10;
  if (mapTerms.some((term) => term.length > 3 && compact.includes(term))) score += 9;
  score += wikiObjectiveTokenOverlap(filename, objectiveTexts) * 3;
  if (/(location|place|spot|room|camera|extract|map|objective|mark|plant)/i.test(lower)) score += 4;
  if (/(reward|dialogue|inspect|requirement)/i.test(lower)) score -= 8;
  return score > 0 ? score : Number.NEGATIVE_INFINITY;
}

function wikiTaskSpansMultipleMaps(marker) {
  if (marker.source === "storyline") {
    const taskId = marker.rowKey.slice("storyline:".length);
    const quest = plannerState.storyline.quests.find((item) => item.id === taskId);
    return quest ? new Set(questMapSlugs(quest).filter((slug) => slug !== "anywhere")).size > 1 : false;
  }
  const taskId = marker.rowKey.slice("regular:".length);
  const task = plannerState.regular.tasks.find((item) => item.id === taskId);
  if (!task) return false;
  const slugs = new Set();
  if (task.map) slugs.add(mapSlug(task.map.normalizedName || task.map.name));
  for (const objective of task.objectives || []) {
    for (const map of objective.maps || []) slugs.add(mapSlug(map.normalizedName || map.name));
    for (const location of objective.locations || []) slugs.add(locationMapSlug(location));
  }
  slugs.delete("anywhere");
  return slugs.size > 1;
}

function wikiImageMatchesObjectives(filename, objectiveTexts) {
  return wikiObjectiveTokenOverlap(filename, objectiveTexts) >= 2;
}

function wikiObjectiveTokenOverlap(filename, objectiveTexts) {
  const imageTokens = new Set(wikiSearchTokens(filename));
  const objectiveTokens = new Set((objectiveTexts || []).flatMap(wikiSearchTokens));
  return [...imageTokens].filter((token) => objectiveTokens.has(token)).length;
}

function wikiSearchTokens(value) {
  const ignored = new Set([
    "break", "chain", "quest", "task", "image", "location", "objective", "shoot",
    "find", "place", "plant", "mark", "transmitter", "repeater", "near", "from",
    "with", "into", "data", "used", "same", "the", "and", "for",
  ]);
  return looseSlug(value)
    .split("-")
    .filter((token) => token.length >= 4 && !ignored.has(token));
}

function wikiImageRights(metadata = {}) {
  const license = cleanWikiMetadata(metadata.LicenseShortName?.value || metadata.UsageTerms?.value);
  const artist = cleanWikiMetadata(metadata.Artist?.value || metadata.Credit?.value);
  if (license && artist) return `${license} · ${artist}`;
  return license || artist || "Rights details on file page";
}

function cleanWikiMetadata(value) {
  if (!value) return "";
  const documentFragment = new DOMParser().parseFromString(`<body>${value}</body>`, "text/html");
  return documentFragment.body.textContent.replace(/\s+/g, " ").trim().slice(0, 100);
}

function wikiImageMatchesMap(filename, selectedMap) {
  const compact = looseSlug(filename);
  const config = plannerState.configBySlug.get(selectedMap);
  return [config?.name, ...(config?.aliases || [])]
    .filter(Boolean)
    .map(looseSlug)
    .some((term) => term.length > 3 && compact.includes(term));
}

function scheduleWikiHide() {
  window.clearTimeout(wikiHideTimer);
  wikiHideTimer = window.setTimeout(hideWikiPreview, 900);
}

function cancelWikiHide() {
  window.clearTimeout(wikiHideTimer);
}

function hideWikiPreview(options = {}) {
  window.clearTimeout(wikiHoverTimer);
  window.clearTimeout(wikiHideTimer);
  wikiRequestToken += 1;
  activeWikiTrigger?.setAttribute("aria-expanded", "false");
  plannerDom.wikiHoverPreview.hidden = true;
  if (options.restoreFocus && activeWikiTrigger?.isConnected) activeWikiTrigger.focus();
  activeWikiTrigger = null;
}

function focusDeepLinkedTask() {
  if (!plannerState.focusedTaskKey) return;
  const card = document.getElementById(`pool-${domSafe(plannerState.focusedTaskKey)}`);
  if (!card) return;
  const focusKey = plannerState.focusedTaskKey;
  plannerState.focusedTaskKey = null;
  window.requestAnimationFrame(() => {
    card.scrollIntoView({ block: "nearest" });
    card.focus({ preventScroll: true });
    const row = plannerState.visibleRows.find((item) => item.key === focusKey);
    if (row?.markers.length) showTaskOnMap(focusKey);
  });
}

function updatePlannerUrl(options = {}) {
  const url = new URL(window.location.href);
  url.searchParams.set("map", plannerState.selectedMap);
  if (plannerState.filters.source === "all") url.searchParams.delete("source");
  else url.searchParams.set("source", plannerState.filters.source);
  if (options.clearTask) url.searchParams.delete("task");
  window.history.replaceState(null, "", url);
}

function sourceTaskHref(row) {
  return row.source === "storyline"
    ? `./index.html#quest-${encodeURIComponent(row.taskId)}`
    : `./regular.html#task-${encodeURIComponent(row.taskId)}`;
}

function locationMapSlug(location) {
  return plannerState.mapIdToSlug.get(location.mapId) || mapSlug(location.mapName);
}

function mapSlug(value) {
  const loose = looseSlug(value);
  if (!loose) return null;
  if (plannerState.aliasToSlug.has(loose)) return plannerState.aliasToSlug.get(loose);
  if (loose.startsWith("ground-zero")) return "ground-zero";
  if (loose === "night-factory") return "factory";
  if (loose === "streets") return "streets-of-tarkov";
  if (loose === "labs" || loose === "laboratory") return "the-lab";
  if (loose.includes("black-division")) return null;
  return loose;
}

function looseSlug(value) {
  return String(value || "")
    .trim()
    .toLowerCase()
    .replace(/&/g, " and ")
    .replace(/\+/g, "-plus")
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "");
}

function hasFinitePosition(value) {
  return value && value.x !== null && value.x !== undefined && value.z !== null && value.z !== undefined &&
    Number.isFinite(Number(value.x)) && Number.isFinite(Number(value.z));
}

function finiteOrNull(value) {
  return value !== null && value !== undefined && Number.isFinite(Number(value)) ? Number(value) : null;
}

function readPlan() {
  const value = readValue(PLANNER_STORAGE.plan, "[]");
  try {
    const parsed = JSON.parse(value);
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

function readArray(key) {
  const value = readValue(key, "[]");
  try {
    const parsed = JSON.parse(value);
    return Array.isArray(parsed) ? parsed : [];
  } catch {
    return [];
  }
}

function readObject(key) {
  const value = readValue(key, "{}");
  try {
    const parsed = JSON.parse(value);
    return parsed && typeof parsed === "object" && !Array.isArray(parsed) ? parsed : {};
  } catch {
    return {};
  }
}

function readValue(key, fallback) {
  try {
    return window.localStorage.getItem(key) ?? fallback;
  } catch {
    return fallback;
  }
}

function writeValue(key, value) {
  try {
    window.localStorage.setItem(key, value);
  } catch {
    showPlannerToast("Browser storage is unavailable; this raid plan cannot persist.");
  }
}

function formatDate(value) {
  if (!value) return "current";
  const date = new Date(value);
  return Number.isNaN(date.getTime())
    ? String(value)
    : new Intl.DateTimeFormat("en-GB", { day: "2-digit", month: "short", year: "numeric" }).format(date);
}

function cleanImageName(value) {
  return String(value || "Wiki location image")
    .replace(/\.[^.]+$/, "")
    .replace(/[_-]+/g, " ")
    .trim();
}

function capitalizePlanner(value) {
  return value ? value.charAt(0).toUpperCase() + value.slice(1) : value;
}

function domSafe(value) {
  return String(value).replace(/[^a-zA-Z0-9_-]/g, "-");
}

function cssEscape(value) {
  return window.CSS?.escape ? window.CSS.escape(value) : String(value).replace(/["\\]/g, "\\$&");
}

function escapePlanner(value) {
  return String(value ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;")
    .replace(/'/g, "&#039;");
}

function showPlannerToast(message) {
  window.clearTimeout(plannerToastTimer);
  plannerDom.plannerToast.textContent = message;
  plannerDom.plannerToast.classList.add("is-visible");
  plannerToastTimer = window.setTimeout(() => plannerDom.plannerToast.classList.remove("is-visible"), 2600);
}
