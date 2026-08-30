const REGULAR_STORAGE = {
  completed: "kord-breach:regular-completed",
  level: "kord-breach:player-level",
  faction: "kord-breach:player-faction",
  reputation: "kord-breach:trader-reputation",
  source: "kord-breach:completion-source",
};

const STORYLINE_STORAGE = {
  completed: "kord-breach:completed",
  securedLoot: "kord-breach:secured-loot",
  route: "kord-breach:route",
};

const regularState = {
  data: null,
  completed: new Set(readArray(REGULAR_STORAGE.completed)),
  playerLevel: Number(readValue(REGULAR_STORAGE.level, 1)) || 1,
  faction: readValue(REGULAR_STORAGE.faction, "Any"),
  reputation: readObject(REGULAR_STORAGE.reputation),
  completionSource: readObject(REGULAR_STORAGE.source),
  filters: { search: "", trader: "", map: "", status: "" },
  limit: 100,
};

const regularDom = {};
let regularToastTimer;
let regularSearchTimer;

document.addEventListener("DOMContentLoaded", initializeRegularPlanner);

async function initializeRegularPlanner() {
  cacheRegularDom();
  bindRegularEvents();
  setExplorerControlsDisabled(true);

  try {
    const response = await fetch("./data/regular_quest_progression.json");
    if (!response.ok) throw new Error(`Progression data returned ${response.status}`);
    regularState.data = await response.json();
    hydrateRegularControls();
    setExplorerControlsDisabled(false);
    renderRegularPlanner();
    window.requestAnimationFrame(() => handleTaskHash({ focus: false }));
  } catch (error) {
    regularDom.taskList.innerHTML =
      '<div class="empty-state"><strong>Task intelligence unavailable</strong><p>Run the static build so the researched seasonal snapshot is included.</p></div>';
    regularDom.resultCount.textContent = "Task data failed to load";
    console.error(error);
  }
}

function cacheRegularDom() {
  const ids = [
    "active-filter-count",
    "clear-regular-filters",
    "completed-total",
    "completion-source",
    "export-regular",
    "group-gate-total",
    "import-regular",
    "load-more",
    "open-total",
    "player-faction",
    "player-level",
    "regular-empty",
    "regular-map",
    "regular-result-count",
    "regular-search",
    "regular-status",
    "regular-task-list",
    "regular-toast",
    "regular-trader",
    "rep-opportunities",
    "reset-regular",
    "snapshot-date",
    "task-total",
    "trader-board",
    "trader-standings",
    "trader-summary",
  ];

  for (const id of ids) regularDom[toCamel(id)] = document.getElementById(id);
  Object.assign(regularDom, {
    empty: regularDom.regularEmpty,
    map: regularDom.regularMap,
    resultCount: regularDom.regularResultCount,
    search: regularDom.regularSearch,
    status: regularDom.regularStatus,
    taskList: regularDom.regularTaskList,
    toast: regularDom.regularToast,
    trader: regularDom.regularTrader,
  });
}

function bindRegularEvents() {
  regularDom.playerLevel.addEventListener("change", (event) => {
    regularState.playerLevel = clamp(Number(event.target.value) || 1, 1, 100);
    event.target.value = regularState.playerLevel;
    writeValue(REGULAR_STORAGE.level, regularState.playerLevel);
    renderRegularPlanner();
  });

  regularDom.playerFaction.addEventListener("change", (event) => {
    regularState.faction = event.target.value;
    writeValue(REGULAR_STORAGE.faction, regularState.faction);
    renderRegularPlanner();
  });

  regularDom.traderBoard.addEventListener("change", (event) => {
    const input = event.target.closest("[data-trader-rep]");
    if (!input) return;
    regularState.reputation[input.dataset.traderRep] = round(Number(input.value) || 0);
    writeObject(REGULAR_STORAGE.reputation, regularState.reputation);
    renderRegularPlanner();
  });

  regularDom.search.addEventListener("input", (event) => {
    regularState.filters.search = event.target.value.trim().toLowerCase();
    clearTimeout(regularSearchTimer);
    regularSearchTimer = setTimeout(resetRegularLimit, 100);
  });

  regularDom.trader.addEventListener("click", (event) => {
    const tab = event.target.closest("[data-trader-tab]");
    if (!tab) return;
    regularState.filters.trader = tab.dataset.traderTab;
    resetRegularLimit();
  });

  regularDom.trader.addEventListener("keydown", handleTraderTabKeydown);

  regularDom.map.addEventListener("change", (event) => {
    regularState.filters.map = event.target.value;
    resetRegularLimit();
  });

  regularDom.status.addEventListener("change", (event) => {
    regularState.filters.status = event.target.value;
    resetRegularLimit();
  });

  regularDom.clearRegularFilters.addEventListener("click", () => clearRegularFilters());

  regularDom.taskList.addEventListener("change", (event) => {
    const checkbox = event.target.closest("[data-regular-complete]");
    if (!checkbox) return;

    if (checkbox.checked) regularState.completed.add(checkbox.dataset.regularComplete);
    else regularState.completed.delete(checkbox.dataset.regularComplete);

    writeArray(REGULAR_STORAGE.completed, [...regularState.completed]);
    renderRegularPlanner({ preserveVisibleOrder: true });
  });

  regularDom.loadMore.addEventListener("click", () => {
    regularState.limit += 100;
    renderRegularTasks();
  });

  document.addEventListener("click", handleTaskLinkClick);
  window.addEventListener("hashchange", () => handleTaskHash({ focus: false }));
  regularDom.exportRegular.addEventListener("click", exportRegularProgress);
  regularDom.importRegular.addEventListener("change", importRegularProgress);
  regularDom.resetRegular.addEventListener("click", resetRegularProgress);
}

function hydrateRegularControls() {
  regularDom.playerLevel.value = regularState.playerLevel;
  regularDom.playerFaction.value = regularState.faction;
  regularDom.taskTotal.textContent = regularState.data.meta.taskCount;
  regularDom.groupGateTotal.textContent = regularState.data.stats.tasksWithGlobalGroupGates;
  regularDom.snapshotDate.textContent = new Intl.DateTimeFormat(undefined, {
    day: "2-digit",
    month: "short",
    year: "numeric",
  }).format(new Date(regularState.data.meta.researchedAt));

  const validTaskIds = new Set(regularState.data.tasks.map((task) => task.id));
  regularState.completed = new Set([...regularState.completed].filter((id) => validTaskIds.has(id)));

  const rank = (name) => {
    const index = TRADER_ORDER.indexOf(name);
    return index < 0 ? TRADER_ORDER.length : index;
  };
  const traders = [...new Set(regularState.data.tasks.map((task) => task.traderName))]
    .sort((a, b) => rank(a) - rank(b) || a.localeCompare(b));
  const maps = [...new Set(regularState.data.tasks.map((task) => task.map?.name).filter(Boolean))].sort();

  regularDom.trader.innerHTML = ["", ...traders]
    .map((trader) => `
      <button type="button" role="tab" data-trader-tab="${escapeRegular(trader)}" aria-selected="false" disabled>
        ${escapeRegular(trader || "All")} <span class="tab-count" data-tab-count="${escapeRegular(trader)}"></span>
      </button>
    `).join("");
  regularDom.map.insertAdjacentHTML(
    "beforeend",
    maps.map((map) => `<option value="${escapeRegular(map)}">${escapeRegular(map)}</option>`).join(""),
  );
}

function setExplorerControlsDisabled(disabled) {
  for (const control of [regularDom.search, regularDom.map, regularDom.status]) {
    control.disabled = disabled;
  }
  for (const tab of regularDom.trader.querySelectorAll("[data-trader-tab]")) tab.disabled = disabled;
  regularDom.importRegular.disabled = disabled;
  regularDom.loadMore.disabled = disabled;
  updateFilterUi();
}

function renderRegularPlanner(options = {}) {
  if (!regularState.data) return;
  const context = buildAvailabilityContext();
  const openCount = regularState.data.tasks.filter(
    (task) => getAvailability(task, context).status === "available",
  ).length;

  regularDom.openTotal.textContent = openCount;
  regularDom.completedTotal.textContent = regularState.completed.size;
  renderTraderBoard(context);
  renderCompletionSource();
  renderRepOpportunities(context);
  renderRegularTasks(context, options);
}

function buildAvailabilityContext() {
  const traders = new Map(regularState.data.traders.map((trader) => [trader.id, trader]));
  const taskById = new Map(regularState.data.tasks.map((task) => [task.id, task]));
  const groupProgress = new Map();

  for (const taskId of regularState.completed) {
    const groupId = taskById.get(taskId)?.progressionGroupId;
    if (groupId) groupProgress.set(groupId, (groupProgress.get(groupId) || 0) + 1);
  }

  return { traders, taskById, groupProgress };
}

function getTraderLoyalty(trader, reputation = getReputation(trader?.id)) {
  if (!trader?.levels?.length) return 1;
  const available = trader.levels.filter(
    (level) => regularState.playerLevel >= level.requiredPlayerLevel && reputation >= level.requiredReputation,
  );
  return Math.max(...available.map((level) => level.level), 1);
}

function getAvailability(task, context) {
  if (regularState.completed.has(task.id)) return { status: "done", reasons: [] };

  const reasons = [];
  if (regularState.playerLevel < task.minPlayerLevel) {
    reasons.push({ type: "level", label: `PMC level ${task.minPlayerLevel}` });
  }

  if (
    regularState.faction !== "Any" &&
    task.factionName !== "Any" &&
    task.factionName !== regularState.faction
  ) {
    reasons.push({ type: "manual", label: `${task.factionName} only` });
  }

  if (task.requiredPrestige > 0) {
    reasons.push({ type: "manual", label: `Prestige ${task.requiredPrestige}` });
  }

  for (const requirement of task.traderRequirements) {
    const trader = context.traders.get(requirement.traderId);
    const actual = requirement.requirementType === "level"
      ? getTraderLoyalty(trader)
      : getReputation(requirement.traderId);
    if (!compare(actual, requirement.compareMethod, Number(requirement.value))) {
      reasons.push({
        type: "rep",
        label: requirement.requirementType === "level"
          ? `${requirement.traderName} LL${requirement.value}`
          : `${requirement.traderName} rep ${formatRep(requirement.value)}`,
      });
    }
  }

  for (const requirement of task.taskRequirements) {
    const statuses = Array.isArray(requirement.status) ? requirement.status : [requirement.status];
    const prerequisiteComplete = regularState.completed.has(requirement.taskId);
    const acceptsComplete = statuses.includes("complete") || statuses.length === 0;
    const acceptsActive = statuses.includes("active");
    const acceptsFailure = statuses.includes("failed");
    if (acceptsComplete && !prerequisiteComplete) {
      reasons.push({
        type: "prerequisite",
        label: `Complete ${requirement.taskName}`,
        taskId: requirement.taskId,
      });
    } else if (!acceptsComplete && acceptsActive && !prerequisiteComplete) {
      reasons.push({
        type: "prerequisite",
        label: `Accept ${requirement.taskName}`,
        taskId: requirement.taskId,
      });
    } else if (!acceptsComplete && !acceptsActive && acceptsFailure) {
      reasons.push({
        type: "manual",
        label: `${requirement.taskName} branch outcome`,
        taskId: requirement.taskId,
      });
    }
  }

  for (const requirement of task.globalRequirements) {
    const actual = context.groupProgress.get(requirement.groupId) || 0;
    if (!compare(actual, requirement.compareMethod, requirement.value)) {
      reasons.push({
        type: "group",
        label: `LL${requirement.loyaltyTier || "?"} task group ${actual}/${requirement.value}`,
      });
    }
  }

  if (task.globalRequirements.length && task.progressionTier) {
    const trader = context.traders.get(task.traderId);
    if (trader && getTraderLoyalty(trader) < task.progressionTier) {
      reasons.push({ type: "rep", label: `${task.traderName} LL${task.progressionTier}` });
    }
  }

  if (task.dialogueRequirements.length) {
    reasons.push({
      type: "manual",
      label: `Trader dialogue: ${task.dialogueRequirements.flatMap((item) => item.traderNames).join(", ")}`,
    });
  }
  if (task.hasUnresolvedRequirement) {
    reasons.push({ type: "manual", label: "Special in-game condition" });
  }

  const priority = ["rep", "level", "prerequisite", "group", "manual"];
  const status = priority.find((type) => reasons.some((reason) => reason.type === type)) || "available";
  return { status, reasons };
}

function renderTraderBoard(context) {
  let maximumLoyaltyCount = 0;
  const knownTraderIds = new Set(regularState.data.traders.map((trader) => trader.id));
  const traders = [...regularState.data.traders].sort((a, b) => {
    const aRank = TRADER_ORDER.indexOf(a.name);
    const bRank = TRADER_ORDER.indexOf(b.name);
    return (aRank < 0 ? TRADER_ORDER.length : aRank) -
      (bRank < 0 ? TRADER_ORDER.length : bRank) || a.name.localeCompare(b.name);
  });
  const configuredCount = Object.keys(regularState.reputation)
    .filter((traderId) => knownTraderIds.has(traderId)).length;

  regularDom.traderBoard.innerHTML = traders.map((trader) => {
    const reputation = getReputation(trader.id);
    const loyalty = getTraderLoyalty(trader, reputation);
    const next = trader.levels.find((level) => level.level > loyalty);
    if (!next) maximumLoyaltyCount += 1;
    const currentLevel = trader.levels.find((level) => level.level === loyalty) || trader.levels[0];
    const rangeStart = currentLevel?.requiredReputation || 0;
    const rangeEnd = next?.requiredReputation ?? rangeStart;
    const progress = next
      ? clamp(((reputation - rangeStart) / Math.max(rangeEnd - rangeStart, 0.01)) * 100, 0, 100)
      : 100;
    const levelGap = next ? Math.max(0, next.requiredPlayerLevel - regularState.playerLevel) : 0;
    const repGap = next ? round(Math.max(0, next.requiredReputation - reputation)) : 0;
    const group = regularState.data.progressionGroups.find(
      (item) => item.traderId === trader.id && item.loyaltyTier === loyalty,
    );
    const groupCount = group ? context.groupProgress.get(group.id) || 0 : 0;

    return `
      <article class="trader-card ${next ? "" : "is-max"}">
        <div class="trader-head">
          <h3>${escapeRegular(trader.name)}</h3>
          <span class="ll-badge">LL${loyalty}</span>
        </div>
        <div class="trader-input-row">
          <label><span>Current standing</span><input class="trader-rep-input" data-trader-rep="${escapeRegular(trader.id)}" aria-label="${escapeRegular(trader.name)} current reputation" type="number" min="-20" max="99" step="0.01" inputmode="decimal" value="${reputation}"></label>
          <span class="rep-gain">${next ? `${formatRep(repGap)} left` : "MAX LL"}</span>
        </div>
        <div class="trader-progress" role="progressbar" aria-label="${escapeRegular(trader.name)} progress to next loyalty level" aria-valuemin="0" aria-valuemax="100" aria-valuenow="${Math.round(progress)}"><span style="--width:${progress}%"></span></div>
        <div class="trader-next">
          <span>${next ? `Next: LL${next.level}` : "All loyalty levels reached"}</span>
          <strong>${next ? `${formatRep(next.requiredReputation)} rep · L${next.requiredPlayerLevel}` : "Complete"}</strong>
        </div>
        ${levelGap ? `<p class="trader-group-line">Needs ${levelGap} more PMC level${levelGap === 1 ? "" : "s"}.</p>` : ""}
        ${group ? `<p class="trader-group-line">Estimated LL${loyalty} task counter: <strong>${groupCount}/${group.maximumRequiredCompletions}</strong> · gates ${group.thresholds.join(" / ")}</p>` : ""}
      </article>
    `;
  }).join("");

  regularDom.traderSummary.textContent = configuredCount
    ? `${configuredCount}/${traders.length} entered · ${maximumLoyaltyCount} at max LL`
    : `Enter current reputation · ${traders.length} traders`;
}

function renderRepOpportunities(context) {
  const opportunities = regularState.data.tasks
    .filter((task) => getAvailability(task, context).status === "available")
    .map((task) => ({
      task,
      gains: task.finishStanding.filter((reward) => reward.standing > 0),
      maximum: Math.max(0, ...task.finishStanding.map((reward) => reward.standing)),
    }))
    .filter((item) => item.maximum > 0)
    .sort((a, b) => b.maximum - a.maximum || b.task.experience - a.task.experience)
    .slice(0, 8);

  regularDom.repOpportunities.innerHTML = opportunities.length
    ? opportunities.map((item, index) => `
        <a class="rep-opportunity" href="#${taskAnchor(item.task.id)}" data-task-link="${escapeRegular(item.task.id)}">
          <span class="rank">${String(index + 1).padStart(2, "0")}</span>
          <span><strong>${escapeRegular(item.task.name)}</strong><small>${escapeRegular(item.task.traderName)}${item.task.map ? ` · ${escapeRegular(item.task.map.name)}` : ""}</small></span>
          <span class="rep-gain">${item.gains.map((reward) => `${formatSignedRep(reward.standing)} ${escapeRegular(reward.traderName)}`).join(" / ")}</span>
          <span class="opportunity-arrow" aria-hidden="true">→</span>
        </a>
      `).join("")
    : '<p class="panel-intro">No positive-standing tasks are currently open under this PMC profile.</p>';
}

function renderRegularTasks(context = buildAvailabilityContext(), options = {}) {
  if (!regularState.data) return;
  const taskUi = captureTaskUi();
  const depthMemo = new Map();
  const rows = regularState.data.tasks.map((task) => ({
    task,
    availability: getAvailability(task, context),
    depth: prerequisiteDepth(task, context, depthMemo),
  }));
  const matching = rows.filter(matchesRegularFilters).sort(compareProgression);

  if (options.preserveVisibleOrder && taskUi.visibleOrder.length) {
    const previousRank = new Map(taskUi.visibleOrder.map((taskId, index) => [taskId, index]));
    matching.sort((a, b) => {
      const aRank = previousRank.get(a.task.id);
      const bRank = previousRank.get(b.task.id);
      if (aRank !== undefined && bRank !== undefined) return aRank - bRank;
      if (aRank !== undefined) return -1;
      if (bRank !== undefined) return 1;
      return compareProgression(a, b);
    });
  }

  renderTraderTabs(rows);
  const shown = matching.slice(0, regularState.limit);
  regularDom.taskList.innerHTML = shown
    .map(({ task, availability }) => regularTaskMarkup(
      task,
      availability,
      context,
      taskUi.expanded.has(task.id),
    ))
    .join("");

  regularDom.resultCount.textContent = shown.length === matching.length
    ? `${matching.length} matching · ${regularState.data.tasks.length} total`
    : `${shown.length} shown · ${matching.length} matching · ${regularState.data.tasks.length} total`;
  regularDom.empty.hidden = matching.length > 0;
  regularDom.loadMore.hidden = shown.length >= matching.length;
  regularDom.loadMore.disabled = shown.length >= matching.length;
  if (shown.length < matching.length) {
    regularDom.loadMore.textContent = `Load 100 more (${matching.length - shown.length} remaining)`;
  }
  updateFilterUi();
  restoreTaskUi(taskUi);
}

function captureTaskUi() {
  const expanded = new Set(
    [...regularDom.taskList.querySelectorAll("[data-task-details][open]")]
      .map((details) => details.dataset.taskDetails),
  );
  const visibleOrder = [...regularDom.taskList.querySelectorAll("[data-task-card]")]
    .map((card) => card.dataset.taskCard);
  const activeCheckbox = document.activeElement?.closest?.("[data-regular-complete]");
  const focusedTaskId = activeCheckbox?.dataset.regularComplete || null;
  const focusedCard = activeCheckbox?.closest("[data-task-card]");

  return {
    expanded,
    visibleOrder,
    focusedTaskId,
    focusedIndex: focusedTaskId ? visibleOrder.indexOf(focusedTaskId) : -1,
    focusedTop: focusedCard?.getBoundingClientRect().top ?? null,
  };
}

function restoreTaskUi(taskUi) {
  if (!taskUi.focusedTaskId) return;
  const checkboxes = [...regularDom.taskList.querySelectorAll("[data-regular-complete]")];
  let nextFocus = checkboxes.find(
    (checkbox) => checkbox.dataset.regularComplete === taskUi.focusedTaskId,
  );
  if (!nextFocus && checkboxes.length) {
    nextFocus = checkboxes[Math.min(Math.max(taskUi.focusedIndex, 0), checkboxes.length - 1)];
  }
  if (!nextFocus) {
    regularDom.resultCount.setAttribute("tabindex", "-1");
    regularDom.resultCount.focus({ preventScroll: true });
    return;
  }

  const nextCard = nextFocus.closest("[data-task-card]");
  if (taskUi.focusedTop !== null && nextCard) {
    const offset = nextCard.getBoundingClientRect().top - taskUi.focusedTop;
    if (Math.abs(offset) > 1) window.scrollBy(0, offset);
  }
  nextFocus.focus({ preventScroll: true });
}

const STATUS_RANK = { available: 0, done: 2 };
function compareProgression(a, b) {
  return (
    (STATUS_RANK[a.availability.status] ?? 1) - (STATUS_RANK[b.availability.status] ?? 1) ||
    a.depth - b.depth ||
    a.task.minPlayerLevel - b.task.minPlayerLevel ||
    a.task.traderName.localeCompare(b.task.traderName) ||
    a.task.name.localeCompare(b.task.name)
  );
}

function prerequisiteDepth(task, context, memo) {
  if (regularState.completed.has(task.id)) return 0;
  if (memo.has(task.id)) return memo.get(task.id);
  memo.set(task.id, 0);
  let depth = 0;
  for (const requirement of task.taskRequirements) {
    const statuses = Array.isArray(requirement.status) ? requirement.status : [requirement.status];
    if (statuses.length && !statuses.includes("complete")) continue;
    const prerequisite = context.taskById.get(requirement.taskId);
    if (prerequisite && !regularState.completed.has(prerequisite.id)) {
      depth = Math.max(depth, 1 + prerequisiteDepth(prerequisite, context, memo));
    }
  }
  memo.set(task.id, depth);
  return depth;
}

const TRADER_ORDER = ["Prapor", "Therapist", "Fence", "Skier", "Peacekeeper", "Mechanic", "Ragman", "Jaeger", "Ref"];
function renderTraderTabs(rows) {
  const available = new Map();
  for (const { task, availability } of rows) {
    if (availability.status === "available") {
      available.set(task.traderName, (available.get(task.traderName) || 0) + 1);
    }
  }

  const totalAvailable = rows.filter((row) => row.availability.status === "available").length;
  for (const tab of regularDom.trader.querySelectorAll("[data-trader-tab]")) {
    const trader = tab.dataset.traderTab;
    const count = trader
      ? available.get(trader) || 0
      : totalAvailable;
    const active = trader === regularState.filters.trader;
    tab.classList.toggle("is-active", active);
    tab.setAttribute("aria-selected", String(active));
    tab.tabIndex = active ? 0 : -1;
    tab.querySelector(".tab-count").textContent = String(trader ? count : totalAvailable);
  }
}

function handleTraderTabKeydown(event) {
  if (!["ArrowLeft", "ArrowRight", "Home", "End"].includes(event.key)) return;
  const tabs = [...regularDom.trader.querySelectorAll("[data-trader-tab]:not(:disabled)")];
  const current = event.target.closest("[data-trader-tab]");
  if (!current || !tabs.length) return;
  event.preventDefault();
  const index = tabs.indexOf(current);
  const target = event.key === "Home"
    ? tabs[0]
    : event.key === "End"
      ? tabs[tabs.length - 1]
      : tabs[(index + (event.key === "ArrowRight" ? 1 : -1) + tabs.length) % tabs.length];
  target.click();
  target.focus();
}

function matchesRegularFilters({ task, availability }) {
  const searchBlob = [
    task.name,
    task.traderName,
    task.map?.name,
    task.factionName,
    ...availability.reasons.map((reason) => reason.label),
    ...task.finishStanding.map((reward) => `${reward.traderName} ${reward.standing}`),
  ].join(" ").toLowerCase();

  return (
    (!regularState.filters.search || searchBlob.includes(regularState.filters.search)) &&
    (!regularState.filters.trader || task.traderName === regularState.filters.trader) &&
    (!regularState.filters.map || task.map?.name === regularState.filters.map) &&
    (!regularState.filters.status || availability.status === regularState.filters.status)
  );
}

function regularTaskMarkup(task, availability, context, expanded) {
  const complete = availability.status === "done";
  const statusLabel = getStatusLabel(availability.status);
  const gateDescriptions = getGateDescriptions(task, context);
  const rewardChips = [
    ...task.finishStanding.map((reward) => `
      <span class="reward-chip ${reward.standing >= 0 ? "positive" : "negative"}">${formatSignedRep(reward.standing)} ${escapeRegular(reward.traderName)}</span>
    `),
    task.experience ? `<span class="reward-chip">${formatNumber(task.experience)} XP</span>` : "",
  ].filter(Boolean).join("");
  const plannerLocation = task.map?.name || task.objectives?.flatMap((objective) => [
    ...(objective.maps || []).map((map) => map.name),
    ...(objective.locations || []).map((location) => location.mapName),
  ]).find(Boolean);
  const plannerParams = new URLSearchParams({ source: "regular", task: task.id });
  if (plannerLocation) plannerParams.set("map", plannerLocation);
  const plannerHref = `./planner.html?${plannerParams.toString()}`;

  return `
    <article id="${taskAnchor(task.id)}" data-task-card="${escapeRegular(task.id)}" class="regular-task ${complete ? "is-done" : ""} ${availability.status === "available" ? "is-available" : ""}">
      <label class="regular-task-check" title="Mark ${escapeRegular(task.name)} complete">
        <input type="checkbox" data-regular-complete="${escapeRegular(task.id)}" ${complete ? "checked" : ""} aria-label="Mark ${escapeRegular(task.name)} complete">
      </label>
      <details data-task-details="${escapeRegular(task.id)}" ${expanded ? "open" : ""}>
        <summary>
          <span>
            <span class="regular-task-title">${escapeRegular(task.name)}</span>
            <span class="regular-task-meta"><span>${escapeRegular(task.traderName)}</span>${task.map ? `<span>${escapeRegular(task.map.name)}</span>` : ""}${task.progressionTier ? `<span>LL${task.progressionTier} band</span>` : ""}${task.factionName !== "Any" ? `<span>${task.factionName}</span>` : ""}</span>
          </span>
          <span class="status-badge ${complete ? "done" : availability.status === "available" ? "available" : "blocked"}">${statusLabel}</span>
          <span class="disclosure-chevron" aria-hidden="true"></span>
        </summary>
        <div class="regular-task-body">
          <div class="task-detail-block">
            <h3>Current blockers</h3>
            ${availability.reasons.length ? `<ul>${availability.reasons.map((reason) => `<li>${taskReferenceMarkup(reason)}</li>`).join("")}</ul>` : "<p>All modeled requirements are met. Confirm the task with the trader in-game.</p>"}
          </div>
          <div class="task-detail-block">
            <h3>Full gate definition</h3>
            <div class="chip-row">${gateDescriptions.length ? gateDescriptions.map((gate) => gate.taskId
              ? `<a class="gate-chip task-jump" href="#${taskAnchor(gate.taskId)}" data-task-link="${escapeRegular(gate.taskId)}">${escapeRegular(gate.label)}</a>`
              : `<span class="gate-chip">${escapeRegular(gate.label)}</span>`).join("") : '<span class="gate-chip">No explicit gate</span>'}</div>
          </div>
          <div class="task-detail-block">
            <h3>Standing and experience</h3>
            <div class="chip-row">${rewardChips || '<span class="reward-chip">No standing reward</span>'}</div>
          </div>
          <div class="task-detail-block">
            <h3>Quest reference</h3>
            <p>${task.wikiLink ? `<a class="task-source" href="${escapeRegular(task.wikiLink)}" target="_blank" rel="noreferrer">Open current quest reference ↗</a>` : "No quest page linked in the data feed."}</p>
          </div>
          <div class="task-detail-block">
            <h3>Raid planning</h3>
            <p><a class="task-source" href="${escapeRegular(plannerHref)}" aria-label="Plan ${escapeRegular(task.name)} on the tactical map">Plan raid on tactical map →</a></p>
          </div>
        </div>
      </details>
    </article>
  `;
}

function getStatusLabel(status) {
  const labels = {
    done: "Completed",
    available: "Available now",
    rep: "Rep / LL gate",
    level: "PMC level gate",
    prerequisite: "Prerequisite",
    group: "Task-group gate",
    manual: "Manual gate",
  };
  return labels[status] || "Blocked";
}

function taskReferenceMarkup(reference) {
  return reference.taskId
    ? `<a class="task-jump" href="#${taskAnchor(reference.taskId)}" data-task-link="${escapeRegular(reference.taskId)}">${escapeRegular(reference.label)} <span aria-hidden="true">→</span></a>`
    : escapeRegular(reference.label);
}

function getGateDescriptions(task, context) {
  const gates = [];
  if (task.minPlayerLevel > 0) gates.push({ label: `PMC level ${task.minPlayerLevel}` });
  for (const requirement of task.traderRequirements) {
    gates.push({
      label: requirement.requirementType === "level"
        ? `${requirement.traderName} LL${requirement.value}`
        : `${requirement.traderName} rep ${formatRep(requirement.value)}`,
    });
  }
  for (const requirement of task.taskRequirements) {
    const statuses = Array.isArray(requirement.status) ? requirement.status : [requirement.status];
    gates.push({
      label: `${requirement.taskName}: ${statuses.filter(Boolean).join("/") || "complete"}`,
      taskId: requirement.taskId,
    });
  }
  for (const requirement of task.globalRequirements) {
    const progress = context.groupProgress.get(requirement.groupId) || 0;
    gates.push({ label: `LL${requirement.loyaltyTier || "?"} group ≥${requirement.value} (${progress} tracked)` });
  }
  if (task.dialogueRequirements.length) gates.push({ label: "Trader dialogue" });
  if (task.requiredPrestige) gates.push({ label: `Prestige ${task.requiredPrestige}` });
  if (task.hasUnresolvedRequirement) gates.push({ label: "Special condition" });
  return gates;
}

function updateFilterUi() {
  const activeCount = Object.values(regularState.filters).filter(Boolean).length;
  regularDom.activeFilterCount.textContent = `${activeCount} active`;
  regularDom.clearRegularFilters.disabled = !regularState.data || activeCount === 0;
}

function clearRegularFilters({ render = true } = {}) {
  clearTimeout(regularSearchTimer);
  regularState.filters = { search: "", trader: "", map: "", status: "" };
  regularState.limit = 100;
  regularDom.search.value = "";
  regularDom.map.value = "";
  regularDom.status.value = "";
  updateFilterUi();
  if (render && regularState.data) renderRegularTasks();
}

function resetRegularLimit() {
  regularState.limit = 100;
  renderRegularTasks();
}

function handleTaskLinkClick(event) {
  const link = event.target.closest("[data-task-link]");
  if (!link || event.defaultPrevented || event.button !== 0 || event.metaKey || event.ctrlKey || event.shiftKey || event.altKey) return;
  event.preventDefault();
  navigateToTask(link.dataset.taskLink, { historyMode: "push", focus: true });
}

function handleTaskHash({ focus = false } = {}) {
  if (!regularState.data) return;
  const taskId = taskIdFromHash();
  if (taskId) navigateToTask(taskId, { historyMode: null, focus });
}

function navigateToTask(taskId, { historyMode = "push", focus = true } = {}) {
  if (!regularState.data?.tasks.some((task) => task.id === taskId)) return;
  clearRegularFilters({ render: false });
  regularState.limit = regularState.data.tasks.length;
  renderRegularTasks();

  const hash = `#${taskAnchor(taskId)}`;
  if (historyMode === "push") history.pushState(null, "", hash);
  if (historyMode === "replace") history.replaceState(null, "", hash);
  const card = document.getElementById(taskAnchor(taskId));
  const details = card?.querySelector("[data-task-details]");
  if (details) details.open = true;
  window.requestAnimationFrame(() => {
    const reduceMotion = typeof window.matchMedia === "function" &&
      window.matchMedia("(prefers-reduced-motion: reduce)").matches;
    card?.scrollIntoView({ behavior: reduceMotion ? "auto" : "smooth", block: "start" });
    if (focus) card?.querySelector("summary")?.focus({ preventScroll: true });
  });
}

function taskIdFromHash() {
  let hash;
  try {
    hash = decodeURIComponent(window.location.hash);
  } catch {
    return null;
  }
  return hash.startsWith("#task-") ? hash.slice(6) : null;
}

function taskAnchor(taskId) {
  return `task-${taskId}`;
}

function exportRegularProgress() {
  const payload = {
    type: "kord-breach-profile-backup",
    version: 2,
    exportedAt: new Date().toISOString(),
    storyline: {
      completed: readArray(STORYLINE_STORAGE.completed),
      securedLoot: readArray(STORYLINE_STORAGE.securedLoot),
      route: readValue(STORYLINE_STORAGE.route, "fence") === "mechanic" ? "mechanic" : "fence",
    },
    regular: {
      completed: [...regularState.completed],
      playerLevel: regularState.playerLevel,
      faction: regularState.faction,
      reputation: regularState.reputation,
      completionSource: regularState.completionSource,
    },
  };
  const blob = new Blob([JSON.stringify(payload, null, 2)], { type: "application/json" });
  const link = document.createElement("a");
  link.href = URL.createObjectURL(blob);
  link.download = `kord-breach-profile-${new Date().toISOString().slice(0, 10)}.json`;
  link.click();
  URL.revokeObjectURL(link.href);
  showRegularToast("PMC profile backup exported");
}

async function importRegularProgress(event) {
  const [file] = event.target.files;
  event.target.value = "";
  if (!file) return;

  try {
    const payload = JSON.parse(await file.text());
    if (isUnifiedProfileBackup(payload)) {
      importUnifiedProfileBackup(payload);
      regularDom.playerLevel.value = regularState.playerLevel;
      regularDom.playerFaction.value = regularState.faction;
      renderRegularPlanner();
      showRegularToast(`Profile restored · ${regularState.completed.size} all-quest tasks`);
      return;
    }

    const parsed = window.KordCompletionImport.parseCompletionPayload(
      payload,
      regularState.data.tasks,
      regularState.data.playerLevels,
    );
    const isOldRegularBackup = payload?.type === "kord-breach-regular-progress";
    if (!parsed.completedIds.length && !parsed.profileOnly && !isOldRegularBackup) {
      throw new Error("No recognized completed quest IDs were found");
    }

    if (parsed.replaceExisting) regularState.completed = new Set(parsed.completedIds);
    else parsed.completedIds.forEach((taskId) => regularState.completed.add(taskId));
    if (parsed.playerLevel) regularState.playerLevel = clamp(parsed.playerLevel, 1, 100);
    if (parsed.faction) regularState.faction = parsed.faction;
    if (parsed.reputation) regularState.reputation = sanitizeReputation(parsed.reputation);
    regularState.completionSource = {
      format: parsed.format,
      fileName: file.name,
      importedAt: new Date().toISOString(),
      sourceUpdatedAt: parsed.updatedAt,
      explicitCount: parsed.explicitIds.length,
      inferredCount: parsed.inferredIds.length,
      unknownCount: parsed.unknownIds.length,
      profileOnly: parsed.profileOnly,
    };
    persistRegularState();
    regularDom.playerLevel.value = regularState.playerLevel;
    regularDom.playerFaction.value = regularState.faction;
    renderRegularPlanner();
    showRegularToast(
      parsed.profileOnly
        ? "Tarkov.dev profile fields imported; quest completions are not exposed"
        : `Imported ${parsed.explicitIds.length} completed tasks${parsed.inferredIds.length ? ` + ${parsed.inferredIds.length} prerequisites` : ""}`,
    );
  } catch (error) {
    showRegularToast(`Import failed: ${error.message}`);
  }
}

function isUnifiedProfileBackup(payload) {
  return payload?.type === "kord-breach-profile-backup" && Number(payload.version) === 2;
}

function importUnifiedProfileBackup(payload) {
  const storyline = payload.storyline;
  const regular = payload.regular;
  if (
    !storyline ||
    !Array.isArray(storyline.completed) ||
    !Array.isArray(storyline.securedLoot) ||
    !regular ||
    !Array.isArray(regular.completed) ||
    !isPlainObject(regular.reputation) ||
    !isPlainObject(regular.completionSource)
  ) {
    throw new Error("Invalid KORD profile backup structure");
  }

  const validTaskIds = new Set(regularState.data.tasks.map((task) => task.id));
  const completed = regular.completed.filter(
    (taskId) => typeof taskId === "string" && validTaskIds.has(taskId),
  );
  const playerLevel = clamp(Number(regular.playerLevel) || 1, 1, 100);
  const faction = ["USEC", "BEAR"].includes(regular.faction) ? regular.faction : "Any";
  const reputation = sanitizeReputation(regular.reputation);
  const completionSource = { ...regular.completionSource };
  const storylineCompleted = storyline.completed.filter((id) => typeof id === "string");
  const securedLoot = storyline.securedLoot.filter((name) => typeof name === "string");
  const route = storyline.route === "mechanic" ? "mechanic" : "fence";

  regularState.completed = new Set(completed);
  regularState.playerLevel = playerLevel;
  regularState.faction = faction;
  regularState.reputation = reputation;
  regularState.completionSource = completionSource;
  persistRegularState();
  writeArray(STORYLINE_STORAGE.completed, storylineCompleted);
  writeArray(STORYLINE_STORAGE.securedLoot, securedLoot);
  writeValue(STORYLINE_STORAGE.route, route);
}

function sanitizeReputation(value) {
  if (!isPlainObject(value)) return {};
  const knownTraderIds = new Set(regularState.data?.traders.map((trader) => trader.id) || []);
  return Object.fromEntries(
    Object.entries(value)
      .filter(([traderId, reputation]) => knownTraderIds.has(traderId) && Number.isFinite(Number(reputation)))
      .map(([traderId, reputation]) => [traderId, round(Number(reputation))]),
  );
}

function isPlainObject(value) {
  return value && typeof value === "object" && !Array.isArray(value);
}

function resetRegularProgress() {
  if (!window.confirm("Reset all-quest completion, PMC level, faction and trader standings on this device? Storyline progress will be kept.")) return;
  regularState.completed.clear();
  regularState.playerLevel = 1;
  regularState.faction = "Any";
  regularState.reputation = {};
  regularState.completionSource = {};
  persistRegularState();
  regularDom.playerLevel.value = 1;
  regularDom.playerFaction.value = "Any";
  regularDom.traderStandings.open = true;
  renderRegularPlanner();
  showRegularToast("All-quest task board reset; storyline kept");
}

function persistRegularState() {
  writeArray(REGULAR_STORAGE.completed, [...regularState.completed]);
  writeValue(REGULAR_STORAGE.level, regularState.playerLevel);
  writeValue(REGULAR_STORAGE.faction, regularState.faction);
  writeObject(REGULAR_STORAGE.reputation, regularState.reputation);
  writeObject(REGULAR_STORAGE.source, regularState.completionSource);
}

function renderCompletionSource() {
  const source = regularState.completionSource;
  regularDom.completionSource.classList.toggle("is-imported", Boolean(source?.format && !source.profileOnly));
  regularDom.completionSource.classList.toggle("is-profile-only", Boolean(source?.profileOnly));

  if (!source?.format) {
    regularDom.completionSource.innerHTML =
      '<span class="source-light" aria-hidden="true"></span><div><strong>Manual tracking</strong><small>No completion file imported yet.</small></div>';
    return;
  }

  const label = completionFormatLabel(source.format);
  const counts = source.profileOnly
    ? "Profile fields only · no quest IDs exposed"
    : `${source.explicitCount || 0} matched${source.inferredCount ? ` · ${source.inferredCount} inferred` : ""}${source.unknownCount ? ` · ${source.unknownCount} unknown ignored` : ""}`;
  regularDom.completionSource.innerHTML = `
    <span class="source-light" aria-hidden="true"></span>
    <div><strong>${escapeRegular(label)}</strong><small>${escapeRegular(source.fileName || "Imported JSON")} · ${escapeRegular(counts)}</small></div>
  `;
}

function completionFormatLabel(format) {
  const labels = {
    "original-raid-optimizer": "Original optimizer progress",
    "kappa-tracker-export": "Kappa tracker completion feed",
    "completed-quests-export": "Completed quests export",
    "task-id-list": "Quest ID list",
    "completed-array": "Completed quests array",
    "tracker-backup": "KORD task-board backup",
    "unified-profile-backup": "KORD PMC profile backup",
    "tarkov-tracker-status-map": "TarkovTracker status map",
    "task-status-map": "Quest status map",
    "tarkov-dev-profile": "Tarkov.dev player profile",
  };
  return labels[format] || "Imported completion data";
}

function getReputation(traderId) {
  return round(Number(regularState.reputation[traderId]) || 0);
}

function compare(actual, method, expected) {
  if (method === ">") return actual > expected;
  if (method === "<") return actual < expected;
  if (method === "<=") return actual <= expected;
  if (["=", "==", "==="].includes(method)) return actual === expected;
  if (method === "!=") return actual !== expected;
  return actual >= expected;
}

function readValue(key, fallback) {
  try {
    return localStorage.getItem(key) ?? fallback;
  } catch {
    return fallback;
  }
}

function readArray(key) {
  try {
    const value = JSON.parse(localStorage.getItem(key) || "[]");
    return Array.isArray(value) ? value : [];
  } catch {
    return [];
  }
}

function readObject(key) {
  try {
    const value = JSON.parse(localStorage.getItem(key) || "{}");
    return isPlainObject(value) ? value : {};
  } catch {
    return {};
  }
}

function writeValue(key, value) {
  try {
    localStorage.setItem(key, String(value));
  } catch {
    showRegularToast("Browser storage is unavailable");
  }
}

function writeArray(key, value) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
  } catch {
    showRegularToast("Browser storage is unavailable");
  }
}

function writeObject(key, value) {
  try {
    localStorage.setItem(key, JSON.stringify(value));
  } catch {
    showRegularToast("Browser storage is unavailable");
  }
}

function showRegularToast(message) {
  regularDom.toast.textContent = message;
  regularDom.toast.classList.add("is-visible");
  clearTimeout(regularToastTimer);
  regularToastTimer = setTimeout(() => regularDom.toast.classList.remove("is-visible"), 2800);
}

function escapeRegular(value) {
  return String(value ?? "").replace(/[&<>"]/g, (character) => ({
    "&": "&amp;",
    "<": "&lt;",
    ">": "&gt;",
    '"': "&quot;",
  })[character]);
}

function toCamel(value) {
  return value.replace(/-([a-z])/g, (_, letter) => letter.toUpperCase());
}

function formatRep(value) {
  return Number(value).toFixed(2);
}

function formatSignedRep(value) {
  const number = Number(value);
  return `${number >= 0 ? "+" : ""}${number.toFixed(2)}`;
}

function formatNumber(value) {
  return new Intl.NumberFormat().format(value);
}

function round(value) {
  return Math.round((value + Number.EPSILON) * 100) / 100;
}

function clamp(value, minimum, maximum) {
  return Math.min(maximum, Math.max(minimum, value));
}
