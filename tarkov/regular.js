const REGULAR_STORAGE = {
  completed: "kord-breach:regular-completed",
  level: "kord-breach:player-level",
  faction: "kord-breach:player-faction",
  reputation: "kord-breach:trader-reputation",
  source: "kord-breach:completion-source",
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

document.addEventListener("DOMContentLoaded", initializeRegularPlanner);

async function initializeRegularPlanner() {
  cacheRegularDom();
  bindRegularEvents();

  try {
    const response = await fetch("./data/regular_quest_progression.json");
    if (!response.ok) throw new Error(`Progression data returned ${response.status}`);
    regularState.data = await response.json();
    hydrateRegularControls();
    renderRegularPlanner();
  } catch (error) {
    regularDom.taskList.innerHTML =
      '<div class="empty-state"><strong>Progression data unavailable</strong><p>Run the static build so the researched task snapshot is included.</p></div>';
    regularDom.resultCount.textContent = "Load failed";
    console.error(error);
  }
}

function cacheRegularDom() {
  const ids = [
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
    resetRegularLimit();
  });

  regularDom.trader.addEventListener("change", (event) => {
    regularState.filters.trader = event.target.value;
    resetRegularLimit();
  });

  regularDom.map.addEventListener("change", (event) => {
    regularState.filters.map = event.target.value;
    resetRegularLimit();
  });

  regularDom.status.addEventListener("change", (event) => {
    regularState.filters.status = event.target.value;
    resetRegularLimit();
  });

  regularDom.taskList.addEventListener("click", (event) => {
    if (event.target.closest(".regular-task-check")) event.stopPropagation();
  });

  regularDom.taskList.addEventListener("change", (event) => {
    const checkbox = event.target.closest("[data-regular-complete]");
    if (!checkbox) return;

    if (checkbox.checked) regularState.completed.add(checkbox.dataset.regularComplete);
    else regularState.completed.delete(checkbox.dataset.regularComplete);

    writeArray(REGULAR_STORAGE.completed, [...regularState.completed]);
    renderRegularPlanner();
  });

  regularDom.loadMore.addEventListener("click", () => {
    regularState.limit += 100;
    renderRegularTasks();
  });

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

  const traders = [...new Set(regularState.data.tasks.map((task) => task.traderName))].sort();
  const maps = [...new Set(regularState.data.tasks.map((task) => task.map?.name).filter(Boolean))].sort();

  regularDom.trader.insertAdjacentHTML(
    "beforeend",
    traders.map((trader) => `<option value="${escapeRegular(trader)}">${escapeRegular(trader)}</option>`).join(""),
  );
  regularDom.map.insertAdjacentHTML(
    "beforeend",
    maps.map((map) => `<option value="${escapeRegular(map)}">${escapeRegular(map)}</option>`).join(""),
  );
}

function renderRegularPlanner() {
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
  renderRegularTasks(context);
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

function getTraderLoyalty(trader, reputation = getReputation(trader.id)) {
  if (!trader?.levels?.length) return 1;
  const available = trader.levels.filter(
    (level) =>
      regularState.playerLevel >= level.requiredPlayerLevel &&
      reputation >= level.requiredReputation,
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
      reasons.push({ type: "prerequisite", label: `Complete ${requirement.taskName}` });
    } else if (!acceptsComplete && acceptsActive && !prerequisiteComplete) {
      reasons.push({ type: "prerequisite", label: `Accept ${requirement.taskName}` });
    } else if (!acceptsComplete && !acceptsActive && acceptsFailure) {
      reasons.push({ type: "manual", label: `${requirement.taskName} branch outcome` });
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
  regularDom.traderBoard.innerHTML = regularState.data.traders.map((trader) => {
    const reputation = getReputation(trader.id);
    const loyalty = getTraderLoyalty(trader, reputation);
    const next = trader.levels.find((level) => level.level > loyalty);
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
          <div><p class="eyebrow">Standing profile</p><h3>${escapeRegular(trader.name)}</h3></div>
          <span class="ll-badge">LL${loyalty}</span>
        </div>
        <div class="trader-input-row">
          <label><span>Current reputation</span><input class="trader-rep-input" data-trader-rep="${trader.id}" type="number" min="-20" max="99" step="0.01" value="${reputation}"></label>
          <span class="rep-gain">${next ? `${formatRep(repGap)} left` : "MAX LL"}</span>
        </div>
        <div class="trader-progress" aria-label="${Math.round(progress)} percent to next loyalty level"><span style="--width:${progress}%"></span></div>
        <div class="trader-next">
          <span>${next ? `Next: LL${next.level}` : "All loyalty levels reached"}</span>
          <strong>${next ? `${formatRep(next.requiredReputation)} rep · L${next.requiredPlayerLevel}` : "Complete"}</strong>
        </div>
        ${levelGap ? `<p class="trader-group-line">Also needs ${levelGap} more PMC level${levelGap === 1 ? "" : "s"}.</p>` : ""}
        ${group ? `<p class="trader-group-line">Estimated LL${loyalty} group counter: <strong>${groupCount}/${group.maximumRequiredCompletions}</strong> · unlock steps ${group.thresholds.join(" / ")}</p>` : ""}
      </article>
    `;
  }).join("");
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
        <article class="rep-opportunity">
          <span class="rank">${String(index + 1).padStart(2, "0")}</span>
          <div><strong>${escapeRegular(item.task.name)}</strong><small>${escapeRegular(item.task.traderName)}${item.task.map ? ` · ${escapeRegular(item.task.map.name)}` : ""}</small></div>
          <span class="rep-gain">${item.gains.map((reward) => `${formatSignedRep(reward.standing)} ${escapeRegular(reward.traderName)}`).join(" / ")}</span>
        </article>
      `).join("")
    : '<p class="panel-intro">No positive-reputation tasks are currently open under this profile.</p>';
}

function renderRegularTasks(context = buildAvailabilityContext()) {
  const depthMemo = new Map();
  const matching = regularState.data.tasks
    .map((task) => ({ task, availability: getAvailability(task, context), depth: prerequisiteDepth(task, context, depthMemo) }))
    .filter(matchesRegularFilters)
    .sort(compareProgression);
  const shown = matching.slice(0, regularState.limit);

  regularDom.taskList.innerHTML = shown
    .map(({ task, availability }) => regularTaskMarkup(task, availability, context))
    .join("");
  regularDom.resultCount.textContent = `${shown.length} shown · ${matching.length} matching · ${regularState.data.tasks.length} total`;
  regularDom.empty.hidden = matching.length > 0;
  regularDom.loadMore.hidden = shown.length >= matching.length;
  regularDom.loadMore.textContent = `Load 100 more (${matching.length - shown.length} remaining)`;
}

// In-game order: what you can do now, then what unlocks next, completed at the bottom.
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

// Number of uncompleted prerequisite tasks still between the player and this task (longest chain).
function prerequisiteDepth(task, context, memo) {
  if (regularState.completed.has(task.id)) return 0;
  if (memo.has(task.id)) return memo.get(task.id);
  memo.set(task.id, 0); // ponytail: cycle guard; data has none, but a bad feed must not hang the page
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

function regularTaskMarkup(task, availability, context) {
  const complete = availability.status === "done";
  const statusLabel = complete
    ? "Completed"
    : availability.status === "available"
      ? "Available now"
      : availability.status === "rep"
        ? "Rep / LL gate"
        : availability.status === "level"
          ? "PMC level gate"
          : availability.status === "prerequisite"
            ? "Prerequisite"
            : availability.status === "group"
              ? "Task-group gate"
              : "Manual gate";
  const gateDescriptions = getGateDescriptions(task, context);
  const rewardChips = [
    ...task.finishStanding.map((reward) => `
      <span class="reward-chip ${reward.standing >= 0 ? "positive" : "negative"}">${formatSignedRep(reward.standing)} ${escapeRegular(reward.traderName)}</span>
    `),
    task.experience ? `<span class="reward-chip">${formatNumber(task.experience)} XP</span>` : "",
  ].filter(Boolean).join("");

  return `
    <details class="regular-task ${complete ? "is-done" : ""} ${availability.status === "available" ? "is-available" : ""}">
      <summary>
        <label class="regular-task-check" title="Mark complete">
          <input type="checkbox" data-regular-complete="${task.id}" ${complete ? "checked" : ""} aria-label="Mark ${escapeRegular(task.name)} complete">
        </label>
        <div>
          <h3 class="regular-task-title">${escapeRegular(task.name)}</h3>
          <div class="regular-task-meta"><span>${escapeRegular(task.traderName)}</span>${task.map ? `<span>${escapeRegular(task.map.name)}</span>` : ""}${task.progressionTier ? `<span>LL${task.progressionTier} band</span>` : ""}${task.factionName !== "Any" ? `<span>${task.factionName}</span>` : ""}</div>
        </div>
        <span class="status-badge ${complete ? "done" : availability.status === "available" ? "available" : "blocked"}">${statusLabel}</span>
      </summary>
      <div class="regular-task-body">
        <div class="task-detail-block">
          <h4>Current blockers</h4>
          ${availability.reasons.length ? `<ul>${availability.reasons.map((reason) => `<li>${escapeRegular(reason.label)}</li>`).join("")}</ul>` : "<p>All modeled requirements are met.</p>"}
        </div>
        <div class="task-detail-block">
          <h4>Full gate definition</h4>
          <div class="chip-row">${gateDescriptions.length ? gateDescriptions.map((gate) => `<span class="gate-chip">${escapeRegular(gate)}</span>`).join("") : '<span class="gate-chip">No explicit gate</span>'}</div>
        </div>
        <div class="task-detail-block">
          <h4>Standing and experience</h4>
          <div class="chip-row">${rewardChips || '<span class="reward-chip">No standing reward</span>'}</div>
        </div>
        <div class="task-detail-block">
          <h4>Source</h4>
          <p>${task.wikiLink ? `<a class="task-source" href="${escapeRegular(task.wikiLink)}" target="_blank" rel="noreferrer">Open current quest reference ↗</a>` : "No quest page linked in the data feed."}</p>
        </div>
      </div>
    </details>
  `;
}

function getGateDescriptions(task, context) {
  const gates = [];
  if (task.minPlayerLevel > 0) gates.push(`PMC level ${task.minPlayerLevel}`);
  for (const requirement of task.traderRequirements) {
    gates.push(
      requirement.requirementType === "level"
        ? `${requirement.traderName} LL${requirement.value}`
        : `${requirement.traderName} rep ${formatRep(requirement.value)}`,
    );
  }
  for (const requirement of task.taskRequirements) {
    const statuses = Array.isArray(requirement.status) ? requirement.status : [requirement.status];
    gates.push(`${requirement.taskName}: ${statuses.filter(Boolean).join("/") || "complete"}`);
  }
  for (const requirement of task.globalRequirements) {
    const progress = context.groupProgress.get(requirement.groupId) || 0;
    gates.push(`LL${requirement.loyaltyTier || "?"} group ≥${requirement.value} (${progress} tracked)`);
  }
  if (task.dialogueRequirements.length) gates.push("Trader dialogue");
  if (task.requiredPrestige) gates.push(`Prestige ${task.requiredPrestige}`);
  if (task.hasUnresolvedRequirement) gates.push("Special condition");
  return gates;
}

function resetRegularLimit() {
  regularState.limit = 100;
  renderRegularTasks();
}

function exportRegularProgress() {
  const payload = {
    type: "kord-breach-regular-progress",
    version: 1,
    exportedAt: new Date().toISOString(),
    playerLevel: regularState.playerLevel,
    faction: regularState.faction,
    reputation: regularState.reputation,
    completed: [...regularState.completed],
  };
  const blob = new Blob([JSON.stringify(payload, null, 2)], { type: "application/json" });
  const link = document.createElement("a");
  link.href = URL.createObjectURL(blob);
  link.download = `kord-breach-regular-progress-${new Date().toISOString().slice(0, 10)}.json`;
  link.click();
  URL.revokeObjectURL(link.href);
  showRegularToast("Progress backup exported");
}

async function importRegularProgress(event) {
  const [file] = event.target.files;
  event.target.value = "";
  if (!file) return;

  try {
    const payload = JSON.parse(await file.text());
    const parsed = window.KordCompletionImport.parseCompletionPayload(
      payload,
      regularState.data.tasks,
      regularState.data.playerLevels,
    );

    if (!parsed.completedIds.length && !parsed.profileOnly) {
      throw new Error("No recognized completed quest IDs were found");
    }

    if (parsed.replaceExisting) regularState.completed = new Set(parsed.completedIds);
    else parsed.completedIds.forEach((taskId) => regularState.completed.add(taskId));
    if (parsed.playerLevel) regularState.playerLevel = clamp(parsed.playerLevel, 1, 100);
    if (parsed.faction) regularState.faction = parsed.faction;
    if (parsed.reputation) regularState.reputation = parsed.reputation;
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
        ? "Tarkov.dev profile fields imported; it contains no quest completions"
        : `Imported ${parsed.explicitIds.length} completed tasks${parsed.inferredIds.length ? ` + ${parsed.inferredIds.length} prerequisites` : ""}`,
    );
  } catch (error) {
    showRegularToast(`Import failed: ${error.message}`);
  }
}

function resetRegularProgress() {
  if (!window.confirm("Reset regular task completion, player level and trader reputation on this device?")) return;
  regularState.completed.clear();
  regularState.playerLevel = 1;
  regularState.faction = "Any";
  regularState.reputation = {};
  regularState.completionSource = {};
  persistRegularState();
  regularDom.playerLevel.value = 1;
  regularDom.playerFaction.value = "Any";
  renderRegularPlanner();
  showRegularToast("Regular progression reset");
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
    "tracker-backup": "Kord tracker backup",
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
    return value && typeof value === "object" && !Array.isArray(value) ? value : {};
  } catch {
    return {};
  }
}

function writeValue(key, value) {
  try { localStorage.setItem(key, String(value)); } catch { showRegularToast("Browser storage is unavailable"); }
}

function writeArray(key, value) {
  try { localStorage.setItem(key, JSON.stringify(value)); } catch { showRegularToast("Browser storage is unavailable"); }
}

function writeObject(key, value) {
  try { localStorage.setItem(key, JSON.stringify(value)); } catch { showRegularToast("Browser storage is unavailable"); }
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
