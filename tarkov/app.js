const STORAGE_KEYS = {
  active: "kord-breach:active",
  completed: "kord-breach:completed",
  secured: "kord-breach:secured-loot",
  route: "kord-breach:route",
};

const REGULAR_STORAGE_KEYS = {
  active: "kord-breach:regular-active",
  completed: "kord-breach:regular-completed",
  external: "kord-breach:external-quest-status",
  playerLevel: "kord-breach:player-level",
  faction: "kord-breach:player-faction",
  reputation: "kord-breach:trader-reputation",
  completionSource: "kord-breach:completion-source",
};

const PROFILE_BACKUP_TYPE = "kord-breach-profile-backup";

const state = {
  data: null,
  active: new Set(readStoredArray(STORAGE_KEYS.active)),
  completed: new Set(readStoredArray(STORAGE_KEYS.completed)),
  secured: new Set(readStoredArray(STORAGE_KEYS.secured)),
  route: readStoredValue(STORAGE_KEYS.route, "fence") === "mechanic" ? "mechanic" : "fence",
  expanded: new Set(),
  filters: {
    search: "",
    trader: "",
    map: "",
    status: "all",
  },
};

const dom = {};
let toastTimer;

document.addEventListener("DOMContentLoaded", init);

async function init() {
  cacheDom();
  bindStaticEvents();

  try {
    const response = await fetch("./data/kord_breach_quests.json");
    if (!response.ok) {
      throw new Error(`Quest data returned ${response.status}`);
    }

    state.data = await response.json();
    const validIds = new Set(state.data.quests.map((quest) => quest.id));
    state.completed = new Set([...state.completed].filter((id) => validIds.has(id)));
    state.active = new Set(
      [...state.active].filter((id) => validIds.has(id) && !state.completed.has(id)),
    );
    hydrateFilterOptions();
    renderAll();
    handleQuestHash();
  } catch (error) {
    dom.questList.innerHTML =
      '<div class="empty-state"><strong>Mission data unavailable</strong><p>Build the site from the repository root so the quest dataset is included.</p></div>';
    dom.resultCount.textContent = "Load failed";
    console.error(error);
  }
}

function cacheDom() {
  [
    "clear-filters",
    "completed-count",
    "continue-quest",
    "empty-state",
    "export-progress",
    "import-progress",
    "loot-count",
    "loot-list",
    "map-filter",
    "next-quest",
    "progress-percent",
    "progress-ring",
    "quest-list",
    "reset-progress",
    "result-count",
    "route-count",
    "search-input",
    "toast",
    "trader-filter",
    "unavailable-list",
  ].forEach((id) => {
    dom[toCamelCase(id)] = document.getElementById(id);
  });
}

function bindStaticEvents() {
  dom.searchInput.addEventListener("input", (event) => {
    state.filters.search = event.target.value.trim().toLowerCase();
    renderQuests();
  });

  dom.traderFilter.addEventListener("change", (event) => {
    state.filters.trader = event.target.value;
    renderQuests();
  });

  dom.mapFilter.addEventListener("change", (event) => {
    state.filters.map = event.target.value;
    renderQuests();
  });

  document.querySelectorAll("[data-status]").forEach((button) => {
    button.addEventListener("click", () => {
      state.filters.status = button.dataset.status;
      updatePressedControls("[data-status]", "status", state.filters.status);
      renderQuests();
    });
  });

  document.querySelectorAll("[data-route]").forEach((button) => {
    button.addEventListener("click", () => {
      state.route = button.dataset.route;
      writeStoredValue(STORAGE_KEYS.route, state.route);
      updatePressedControls("[data-route]", "route", state.route);
      renderAll();
      showToast(`${capitalize(state.route)} route selected`);
    });
  });

  document.addEventListener("click", handleQuestNavigationClick);
  window.addEventListener("hashchange", handleQuestHash);
  dom.clearFilters.addEventListener("click", clearFilters);
  dom.questList.addEventListener("click", handleQuestListClick);
  dom.questList.addEventListener("change", handleQuestCompletion);
  dom.lootList.addEventListener("change", handleLootChange);
  dom.exportProgress.addEventListener("click", exportProgress);
  dom.importProgress.addEventListener("change", importProgress);
  dom.resetProgress.addEventListener("click", resetProgress);
}

function hydrateFilterOptions() {
  const traders = [...new Set(state.data.quests.map((quest) => quest.trader))].sort();
  const maps = [
    ...new Set(state.data.quests.flatMap((quest) => quest.maps || [])),
  ].sort();

  dom.traderFilter.insertAdjacentHTML(
    "beforeend",
    traders
      .map((trader) => `<option value="${escapeHtml(trader)}">${escapeHtml(trader)}</option>`)
      .join(""),
  );

  dom.mapFilter.insertAdjacentHTML(
    "beforeend",
    maps.map((map) => `<option value="${escapeHtml(map)}">${escapeHtml(map)}</option>`).join(""),
  );

  updatePressedControls("[data-route]", "route", state.route);
  updatePressedControls("[data-status]", "status", state.filters.status);
}

function renderAll() {
  renderProgress();
  renderLoot();
  renderQuests();
  renderUnavailable();
}

function getRouteQuests() {
  return state.data.quests.filter((quest) => {
    if (quest.name === "Final Stretch") {
      return state.route === "fence";
    }
    if (quest.name === "Consequences of Our Decisions") {
      return state.route === "mechanic";
    }
    return true;
  });
}

function renderProgress() {
  const routeQuests = getRouteQuests();
  const completedCount = routeQuests.filter((quest) => state.completed.has(quest.id)).length;
  const percent = routeQuests.length
    ? Math.round((completedCount / routeQuests.length) * 100)
    : 0;
  const nextQuest = routeQuests.find(
    (quest) => state.active.has(quest.id) && !state.completed.has(quest.id),
  ) || routeQuests.find((quest) => !state.completed.has(quest.id));

  dom.completedCount.textContent = completedCount;
  dom.routeCount.textContent = routeQuests.length;
  dom.progressPercent.textContent = `${percent}%`;
  dom.progressRing.style.setProperty("--progress", `${percent * 3.6}deg`);
  if (nextQuest) {
    dom.nextQuest.innerHTML = `Next operation: <a class="quest-jump" href="#quest-${escapeHtml(nextQuest.id)}" data-quest-jump="${escapeHtml(nextQuest.id)}">${escapeHtml(nextQuest.name)}</a>`;
    dom.continueQuest.dataset.questJump = nextQuest.id;
    dom.continueQuest.disabled = false;
    dom.continueQuest.textContent = "Continue operation";
  } else {
    dom.nextQuest.textContent = "Route complete. Gear up and get back into raid.";
    delete dom.continueQuest.dataset.questJump;
    dom.continueQuest.disabled = true;
    dom.continueQuest.textContent = "Route complete";
  }
}

function renderLoot() {
  const focus = captureLootFocus();
  const loot = getPriorityLoot();
  const securedCount = loot.filter((item) => state.secured.has(item.name)).length;
  dom.lootCount.textContent = `${securedCount} / ${loot.length} secured`;

  dom.lootList.innerHTML = loot
    .map(
      (item) => `
        <div class="loot-item">
          <label class="loot-check">
            <input
              type="checkbox"
              data-loot-name="${escapeHtml(item.name)}"
              ${state.secured.has(item.name) ? "checked" : ""}
            >
            <span class="check-box" aria-hidden="true"></span>
            <span class="loot-name">${escapeHtml(item.name)}</span>
          </label>
          <span class="loot-qty">×${item.quantity}</span>
          <span class="loot-source">Needed for ${item.quests
            .map(
              (quest) => `<a href="#quest-${escapeHtml(quest.id)}" data-quest-jump="${escapeHtml(quest.id)}">${escapeHtml(quest.name)}</a>`,
            )
            .join(", ")}</span>
        </div>
      `,
    )
    .join("");
  restoreLootFocus(focus);
}

function getPriorityLoot() {
  const priorityQuestIds = new Set([
    "key-to-understanding",
    "riding-the-wave",
    "whats-in-the-bag",
    "forbidden-knowledge",
  ]);
  const loot = new Map();

  state.data.quests
    .filter((quest) => priorityQuestIds.has(quest.id))
    .flatMap((quest) =>
      (quest.items || []).map((item) => ({ item, quest })),
    )
    .filter(({ item }) => item.found_in_raid)
    .forEach(({ item, quest }) => {
      const previous = loot.get(item.name);
      loot.set(item.name, {
        name: item.name,
        quantity: Math.max(item.quantity || 1, previous?.quantity || 0),
        quests: mergeQuestSources(previous?.quests || [], quest),
      });
    });

  return [...loot.values()].sort((a, b) => {
    if (a.quantity !== b.quantity) {
      return b.quantity - a.quantity;
    }
    return a.name.localeCompare(b.name);
  });
}

function renderQuests() {
  const focus = captureQuestFocus();
  const routeQuests = getRouteQuests();
  const visible = routeQuests.filter(matchesFilters);

  dom.questList.innerHTML = visible.map(renderQuestCard).join("");
  dom.resultCount.textContent = `${visible.length} of ${routeQuests.length} tasks`;
  dom.emptyState.hidden = visible.length > 0;
  restoreQuestFocus(focus);
}

function matchesFilters(quest) {
  const complete = state.completed.has(quest.id);
  const active = state.active.has(quest.id);
  const searchBlob = JSON.stringify(quest).toLowerCase();

  if (state.filters.search && !searchBlob.includes(state.filters.search)) {
    return false;
  }
  if (state.filters.trader && quest.trader !== state.filters.trader) {
    return false;
  }
  if (state.filters.map && !(quest.maps || []).includes(state.filters.map)) {
    return false;
  }
  if (state.filters.status === "open" && complete) {
    return false;
  }
  if (state.filters.status === "done" && !complete) {
    return false;
  }
  if (state.filters.status === "active" && !active) {
    return false;
  }
  return true;
}

function renderQuestCard(quest) {
  const complete = state.completed.has(quest.id);
  const active = state.active.has(quest.id) && !complete;
  const expanded = state.expanded.has(quest.id);
  const categoryLabel =
    quest.category === "parallel"
      ? "Parallel"
      : quest.category === "branch"
        ? `${capitalize(quest.branch || "")} branch`
        : "Main route";
  const prerequisites = renderPrerequisites(quest);
  const rewardLines = renderRewardLines(quest);
  const plannerHref = `./planner.html?source=storyline&task=${encodeURIComponent(quest.id)}`;

  return `
    <article
      class="quest-card ${complete ? "is-complete" : ""} ${active ? "is-active-in-game" : ""} ${expanded ? "is-expanded" : ""}"
      id="quest-${escapeHtml(quest.id)}"
      data-card-id="${escapeHtml(quest.id)}"
      tabindex="-1"
    >
      <div class="quest-main">
        <div class="quest-number">${String(quest.order).padStart(2, "0")}</div>
        <div>
          <h3 class="quest-title">${escapeHtml(quest.name)}</h3>
          <div class="quest-meta">
            <span class="quest-trader">${escapeHtml(quest.trader)}</span>
            ${active ? '<span class="quest-badge active">Active in game</span>' : ""}
            <span class="quest-badge ${escapeHtml(quest.category)}">${escapeHtml(categoryLabel)}</span>
            ${(quest.maps || []).slice(0, 3).map((map) => `<span class="map-chip">${escapeHtml(map)}</span>`).join("")}
          </div>
        </div>
        <div class="quest-actions">
          <label class="quest-check">
            <input type="checkbox" data-quest-id="${escapeHtml(quest.id)}" ${complete ? "checked" : ""}>
            <span class="check-box" aria-hidden="true"></span>
            <span>Complete</span>
          </label>
          <a class="details-toggle plan-link" href="${escapeHtml(plannerHref)}" aria-label="Plan ${escapeHtml(quest.name)} on the tactical map">Plan raid</a>
          ${complete ? "" : `<button class="details-toggle active-toggle" type="button" data-story-active="${escapeHtml(quest.id)}">${active ? "Clear active" : "Mark active"}</button>`}
          <button
            class="details-toggle"
            type="button"
            data-expand="${escapeHtml(quest.id)}"
            aria-expanded="${String(expanded)}"
            aria-controls="quest-details-${escapeHtml(quest.id)}"
            aria-label="${expanded ? "Hide" : "Show"} details for ${escapeHtml(quest.name)}"
          >${expanded ? "Hide" : "Details"}</button>
        </div>
      </div>

      <div class="quest-details" id="quest-details-${escapeHtml(quest.id)}">
        <section class="detail-block">
          <h3>Requirements</h3>
          <ul>
            ${prerequisites}
            ${(quest.requirements || []).map((requirement) => `<li>${escapeHtml(requirement)}</li>`).join("")}
          </ul>
        </section>
        <section class="detail-block">
          <h3>Objectives</h3>
          <ul>${(quest.objectives || []).map((objective) => `<li>${escapeHtml(objective)}</li>`).join("")}</ul>
        </section>
        <section class="detail-block">
          <h3>Items</h3>
          <ul>
            ${
              (quest.items || []).length
                ? quest.items.map(renderItem).join("")
                : "<li>No required handover item.</li>"
            }
          </ul>
        </section>
        <section class="detail-block">
          <h3>Rewards</h3>
          <ul>${rewardLines}</ul>
        </section>
        <section class="detail-block full">
          <h3>Unlocks & intelligence</h3>
          <ul>
            ${
              [...(quest.unlocks || []), ...(quest.notes || [])].length
                ? [...(quest.unlocks || []), ...(quest.notes || [])]
                    .map((note) => `<li>${escapeHtml(note)}</li>`)
                    .join("")
                : "<li>No further task is currently listed.</li>"
            }
          </ul>
          <p><a class="source-link" href="${escapeHtml(quest.source_url)}" target="_blank" rel="noreferrer">Open source page ↗</a></p>
        </section>
      </div>
    </article>
  `;
}

function renderPrerequisites(quest) {
  const direct = (quest.prerequisites || []).map((requirement) => {
    const action = requirement.status === "active" ? "Accept" : "Complete";
    return `<li>${action} ${escapeHtml(requirement.name)}</li>`;
  });

  const alternatives = quest.prerequisite_any?.length
    ? [
        `<li>Complete either ${quest.prerequisite_any
          .map((requirement) => escapeHtml(requirement.name))
          .join(" or ")}</li>`,
      ]
    : [];

  return [...direct, ...alternatives].join("");
}

function renderItem(item) {
  const quantity = item.quantity || 1;
  const source = item.source ? ` · ${escapeHtml(item.source)}` : "";
  return `
    <li class="item-row">
      <span><span class="reward-value">${quantity}×</span> ${escapeHtml(item.name)}${source}</span>
      ${item.found_in_raid ? '<span class="fir-badge">FiR</span>' : ""}
    </li>
  `;
}

function renderRewardLines(quest) {
  const rewards = quest.rewards || {};
  const lines = [];

  if (rewards.experience) {
    lines.push(`<li><span class="reward-value">${formatNumber(rewards.experience)} EXP</span></li>`);
  }
  if (rewards.roubles) {
    lines.push(`<li><span class="reward-value">₽${formatNumber(rewards.roubles)}</span> base cash</li>`);
  }
  (rewards.items || []).forEach((item) => lines.push(`<li>${escapeHtml(item)}</li>`));
  (rewards.offer_unlocks || []).forEach((item) =>
    lines.push(`<li>Unlock: ${escapeHtml(item)}</li>`),
  );
  (rewards.achievements || []).forEach((item) =>
    lines.push(`<li>Achievement: ${escapeHtml(item)}</li>`),
  );

  return lines.length ? lines.join("") : "<li>No item reward listed.</li>";
}

function renderUnavailable() {
  dom.unavailableList.innerHTML = state.data.known_unavailable_seasonal_tasks
    .map(
      (task) => `
        <article class="unavailable-task">
          <strong>${escapeHtml(task.name)}</strong>
          <span>${escapeHtml(task.status)}${
            task.known_requirements?.length
              ? ` · ${task.known_requirements.map(escapeHtml).join(" · ")}`
              : ""
          }</span>
        </article>
      `,
    )
    .join("");
}

function handleQuestListClick(event) {
  const activeButton = event.target.closest("[data-story-active]");
  if (activeButton) {
    const questId = activeButton.dataset.storyActive;
    if (state.active.has(questId)) state.active.delete(questId);
    else if (!state.completed.has(questId)) state.active.add(questId);
    writeStoredArray(STORAGE_KEYS.active, [...state.active]);
    renderProgress();
    renderQuests();
    showToast(state.active.has(questId) ? "Marked active in game" : "Cleared active state");
    return;
  }
  const button = event.target.closest("[data-expand]");
  if (!button) {
    return;
  }

  const card = button.closest(".quest-card");
  const expanded = card.classList.toggle("is-expanded");
  if (expanded) {
    state.expanded.add(button.dataset.expand);
  } else {
    state.expanded.delete(button.dataset.expand);
  }
  button.setAttribute("aria-expanded", String(expanded));
  button.setAttribute(
    "aria-label",
    `${expanded ? "Hide" : "Show"} details for ${card.querySelector(".quest-title")?.textContent || "task"}`,
  );
  button.textContent = expanded ? "Hide" : "Details";
}

function handleQuestCompletion(event) {
  const input = event.target.closest("[data-quest-id]");
  if (!input) {
    return;
  }

  const quest = state.data.quests.find((item) => item.id === input.dataset.questId);
  if (!quest) {
    return;
  }

  if (input.checked) {
    state.active.delete(quest.id);
    state.completed.add(quest.id);
    if (quest.mutually_exclusive_with) {
      const alternate = state.data.quests.find(
        (item) => item.name === quest.mutually_exclusive_with,
      );
      if (alternate) {
        state.active.delete(alternate.id);
        state.completed.delete(alternate.id);
      }
    }
  } else {
    state.completed.delete(quest.id);
  }

  writeStoredArray(STORAGE_KEYS.active, [...state.active]);
  writeStoredArray(STORAGE_KEYS.completed, [...state.completed]);
  renderProgress();
  renderQuests();
}

function handleLootChange(event) {
  const input = event.target.closest("[data-loot-name]");
  if (!input) {
    return;
  }

  if (input.checked) {
    state.secured.add(input.dataset.lootName);
  } else {
    state.secured.delete(input.dataset.lootName);
  }

  writeStoredArray(STORAGE_KEYS.secured, [...state.secured]);
  renderLoot();
}

function clearFilters() {
  resetFilterControls();
  renderQuests();
}

function resetFilterControls() {
  state.filters = { search: "", trader: "", map: "", status: "all" };
  dom.searchInput.value = "";
  dom.traderFilter.value = "";
  dom.mapFilter.value = "";
  updatePressedControls("[data-status]", "status", state.filters.status);
}

function handleQuestNavigationClick(event) {
  const control = event.target.closest("[data-quest-jump]");
  if (!control || control.disabled) {
    return;
  }

  event.preventDefault();
  navigateToQuest(control.dataset.questJump, { updateHistory: true });
}

function handleQuestHash() {
  if (!state.data) {
    return;
  }

  const prefix = "#quest-";
  if (!window.location.hash.startsWith(prefix)) {
    return;
  }

  let questId;
  try {
    questId = decodeURIComponent(window.location.hash.slice(prefix.length));
  } catch {
    return;
  }
  navigateToQuest(questId, { updateHistory: false });
}

function navigateToQuest(questId, { updateHistory = false } = {}) {
  const quest = state.data?.quests.find((item) => item.id === questId);
  if (!quest) {
    return;
  }

  const requiredRoute = getQuestRoute(quest);
  const routeChanged = Boolean(requiredRoute && state.route !== requiredRoute);
  if (routeChanged) {
    state.route = requiredRoute;
    writeStoredValue(STORAGE_KEYS.route, state.route);
    updatePressedControls("[data-route]", "route", state.route);
  }

  const routeContainsQuest = getRouteQuests().some((item) => item.id === quest.id);
  if (!routeContainsQuest || !matchesFilters(quest)) {
    resetFilterControls();
  }

  state.expanded.add(quest.id);
  if (routeChanged) {
    renderProgress();
  }
  renderQuests();

  const anchor = `#quest-${quest.id}`;
  if (updateHistory && window.location.hash !== anchor) {
    window.history.pushState(null, "", anchor);
  }

  const card = document.getElementById(`quest-${quest.id}`);
  if (!card) {
    return;
  }
  card.scrollIntoView({ behavior: prefersReducedMotion() ? "auto" : "smooth", block: "start" });
  focusElement(card);
}

function getQuestRoute(quest) {
  if (quest.id === "final-stretch") {
    return "fence";
  }
  if (quest.id === "consequences-of-our-decisions") {
    return "mechanic";
  }
  return "";
}

function updatePressedControls(selector, dataKey, selectedValue) {
  document.querySelectorAll(selector).forEach((button) => {
    const selected = button.dataset[dataKey] === selectedValue;
    button.classList.toggle("is-active", selected);
    button.setAttribute("aria-pressed", String(selected));
  });
}

function captureQuestFocus() {
  const active = document.activeElement;
  if (!active || !dom.questList.contains(active)) {
    return null;
  }

  const checkbox = active.closest("[data-quest-id]");
  const activeToggle = active.closest("[data-story-active]");
  const toggle = active.closest("[data-expand]");
  const card = active.closest("[data-card-id]");
  const target = checkbox || activeToggle || toggle || card;
  if (!target) {
    return null;
  }

  const kind = checkbox ? "quest" : activeToggle ? "active" : toggle ? "expand" : "card";
  const attribute = kind === "quest"
    ? "questId"
    : kind === "active"
      ? "storyActive"
      : kind === "expand"
        ? "expand"
        : "cardId";
  const selector = kind === "quest"
    ? "[data-quest-id]"
    : kind === "active"
      ? "[data-story-active]"
      : kind === "expand"
        ? "[data-expand]"
        : "[data-card-id]";
  const peers = [...dom.questList.querySelectorAll(selector)];
  return {
    kind,
    value: target.dataset[attribute],
    index: peers.indexOf(target),
  };
}

function restoreQuestFocus(snapshot) {
  if (!snapshot) {
    return;
  }

  const selector = snapshot.kind === "quest"
    ? "[data-quest-id]"
    : snapshot.kind === "active"
      ? "[data-story-active]"
    : snapshot.kind === "expand"
      ? "[data-expand]"
      : "[data-card-id]";
  const attribute = snapshot.kind === "quest"
    ? "questId"
    : snapshot.kind === "active"
      ? "storyActive"
    : snapshot.kind === "expand"
      ? "expand"
      : "cardId";
  const peers = [...dom.questList.querySelectorAll(selector)];
  const exact = peers.find((item) => item.dataset[attribute] === snapshot.value);
  const fallback = peers[Math.min(Math.max(snapshot.index, 0), peers.length - 1)];
  focusElement(exact || fallback);
}

function captureLootFocus() {
  const active = document.activeElement;
  if (!active || !dom.lootList.contains(active)) {
    return null;
  }
  const input = active.closest("[data-loot-name]");
  if (!input) {
    return null;
  }
  return input.dataset.lootName;
}

function restoreLootFocus(lootName) {
  if (!lootName) {
    return;
  }
  const input = [...dom.lootList.querySelectorAll("[data-loot-name]")]
    .find((item) => item.dataset.lootName === lootName);
  focusElement(input);
}

function focusElement(element) {
  if (!element) {
    return;
  }
  try {
    element.focus({ preventScroll: true });
  } catch {
    element.focus();
  }
}

function prefersReducedMotion() {
  return typeof window.matchMedia === "function" &&
    window.matchMedia("(prefers-reduced-motion: reduce)").matches;
}

function mergeQuestSources(existing, quest) {
  if (!quest || existing.some((item) => item.id === quest.id)) {
    return existing;
  }
  return [...existing, { id: quest.id, name: quest.name }];
}

function exportProgress() {
  const backup = {
    type: PROFILE_BACKUP_TYPE,
    version: 3,
    exportedAt: new Date().toISOString(),
    storyline: {
      active: [...state.active],
      completed: [...state.completed],
      securedLoot: [...state.secured],
      route: state.route,
    },
    regular: {
      active: readStoredArray(REGULAR_STORAGE_KEYS.active).filter(isString),
      completed: readStoredArray(REGULAR_STORAGE_KEYS.completed).filter(isString),
      external: readStoredArray(REGULAR_STORAGE_KEYS.external).filter(isRecord),
      playerLevel: normalizePlayerLevel(
        readStoredValue(REGULAR_STORAGE_KEYS.playerLevel, "1"),
      ),
      faction: normalizeFaction(
        readStoredValue(REGULAR_STORAGE_KEYS.faction, "Any"),
      ),
      reputation: readStoredObject(REGULAR_STORAGE_KEYS.reputation),
      completionSource: readStoredObject(REGULAR_STORAGE_KEYS.completionSource),
    },
  };
  const blob = new Blob([JSON.stringify(backup, null, 2)], {
    type: "application/json",
  });
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement("a");
  anchor.href = url;
  anchor.download = `kord-breach-profile-backup-${new Date().toISOString().slice(0, 10)}.json`;
  anchor.click();
  URL.revokeObjectURL(url);
  showToast("Storyline and All quests profile exported");
}

async function importProgress(event) {
  const [file] = event.target.files;
  event.target.value = "";
  if (!file) {
    return;
  }

  try {
    if (!state.data) {
      throw new Error("Mission data is still loading");
    }
    const backup = JSON.parse(await file.text());
    const parsed = parseProgressBackup(backup);

    const validIds = new Set(state.data.quests.map((quest) => quest.id));
    state.completed = new Set(parsed.storyline.completed.filter((id) => validIds.has(id)));
    state.active = new Set(
      parsed.storyline.active.filter((id) => validIds.has(id) && !state.completed.has(id)),
    );
    state.secured = new Set(parsed.storyline.securedLoot.filter(isString));
    state.route = parsed.storyline.route === "mechanic" ? "mechanic" : "fence";

    writeStoredArray(STORAGE_KEYS.active, [...state.active]);
    writeStoredArray(STORAGE_KEYS.completed, [...state.completed]);
    writeStoredArray(STORAGE_KEYS.secured, [...state.secured]);
    writeStoredValue(STORAGE_KEYS.route, state.route);
    if (parsed.regular) {
      writeRegularBackup(parsed.regular);
    }
    updatePressedControls("[data-route]", "route", state.route);
    renderAll();
    showToast(
      parsed.regular
        ? "Storyline and All quests profile restored"
        : "Legacy storyline backup restored",
    );
  } catch (error) {
    console.error(error);
    showToast("That file is not a valid KORD BREACH backup");
  }
}

function parseProgressBackup(backup) {
  if (!isRecord(backup)) {
    throw new Error("Backup must be a JSON object");
  }

  const looksLikeProfileBackup =
    backup.type === PROFILE_BACKUP_TYPE ||
    [2, 3].includes(backup.version) ||
    "storyline" in backup ||
    "regular" in backup;

  if (looksLikeProfileBackup) {
    if (
      backup.type !== PROFILE_BACKUP_TYPE ||
      ![2, 3].includes(backup.version) ||
      typeof backup.exportedAt !== "string" ||
      !isRecord(backup.storyline) ||
      !isRecord(backup.regular)
    ) {
      throw new Error("Invalid profile backup header");
    }

    const storyline = backup.storyline;
    const regular = backup.regular;
    if (
      !isStringArray(storyline.completed) ||
      !isStringArray(storyline.securedLoot) ||
      !["fence", "mechanic"].includes(storyline.route) ||
      !isStringArray(regular.completed) ||
      (backup.version === 3 && (
        !isStringArray(storyline.active) ||
        !isStringArray(regular.active) ||
        !Array.isArray(regular.external) ||
        !regular.external.every(isRecord)
      )) ||
      !Number.isFinite(Number(regular.playerLevel)) ||
      typeof regular.faction !== "string" ||
      !isRecord(regular.reputation) ||
      !isRecord(regular.completionSource)
    ) {
      throw new Error("Invalid profile backup data");
    }

    return {
      storyline: {
        active: [...new Set(storyline.active || [])],
        completed: [...storyline.completed],
        securedLoot: [...storyline.securedLoot],
        route: storyline.route,
      },
      regular: {
        active: [...new Set(regular.active || [])],
        completed: [...new Set(regular.completed)],
        external: [...(regular.external || [])],
        playerLevel: normalizePlayerLevel(regular.playerLevel),
        faction: normalizeFaction(regular.faction),
        reputation: regular.reputation,
        completionSource: regular.completionSource,
      },
    };
  }

  // Version 1 storyline exports stored these fields at the top level.
  if (!Array.isArray(backup.completed) || !Array.isArray(backup.securedLoot)) {
    throw new Error("Invalid legacy storyline backup");
  }

  return {
    storyline: {
      active: [],
      completed: backup.completed.filter(isString),
      securedLoot: backup.securedLoot.filter(isString),
      route: backup.route === "mechanic" ? "mechanic" : "fence",
    },
    regular: null,
  };
}

function writeRegularBackup(regular) {
  writeStoredArray(REGULAR_STORAGE_KEYS.active, regular.active.filter(isString));
  writeStoredArray(REGULAR_STORAGE_KEYS.completed, regular.completed.filter(isString));
  writeStoredArray(REGULAR_STORAGE_KEYS.external, regular.external.filter(isRecord));
  writeStoredValue(
    REGULAR_STORAGE_KEYS.playerLevel,
    String(normalizePlayerLevel(regular.playerLevel)),
  );
  writeStoredValue(
    REGULAR_STORAGE_KEYS.faction,
    normalizeFaction(regular.faction),
  );
  writeStoredValue(
    REGULAR_STORAGE_KEYS.reputation,
    JSON.stringify(regular.reputation),
  );
  writeStoredValue(
    REGULAR_STORAGE_KEYS.completionSource,
    JSON.stringify(regular.completionSource),
  );
}

function resetProgress() {
  const confirmed = window.confirm(
    "Reset storyline progress, FiR loot checks and the selected route on this device? Your All quests profile will be kept.",
  );
  if (!confirmed) {
    return;
  }

  state.completed.clear();
  state.active.clear();
  state.secured.clear();
  state.route = "fence";
  Object.values(STORAGE_KEYS).forEach((key) => {
    try {
      localStorage.removeItem(key);
    } catch {
      // Browser storage can be unavailable in hardened modes.
    }
  });
  updatePressedControls("[data-route]", "route", state.route);
  renderAll();
  showToast("Storyline progress reset; All quests profile kept");
}

function showToast(message) {
  window.clearTimeout(toastTimer);
  dom.toast.textContent = message;
  dom.toast.classList.add("is-visible");
  toastTimer = window.setTimeout(() => {
    dom.toast.classList.remove("is-visible");
  }, 2400);
}

function readStoredArray(key) {
  try {
    const value = JSON.parse(localStorage.getItem(key) || "[]");
    return Array.isArray(value) ? value : [];
  } catch {
    return [];
  }
}

function readStoredValue(key, fallback) {
  try {
    return localStorage.getItem(key) || fallback;
  } catch {
    return fallback;
  }
}

function readStoredObject(key) {
  try {
    const value = JSON.parse(localStorage.getItem(key) || "{}");
    return isRecord(value) ? value : {};
  } catch {
    return {};
  }
}

function writeStoredArray(key, value) {
  writeStoredValue(key, JSON.stringify(value));
}

function writeStoredValue(key, value) {
  try {
    localStorage.setItem(key, value);
  } catch {
    showToast("Browser storage is unavailable; progress will not persist");
  }
}

function normalizePlayerLevel(value) {
  const level = Number(value);
  if (!Number.isFinite(level)) {
    return 1;
  }
  return Math.min(100, Math.max(1, Math.trunc(level)));
}

function normalizeFaction(value) {
  const faction = String(value || "Any").toUpperCase();
  return faction === "USEC" || faction === "BEAR" ? faction : "Any";
}

function isRecord(value) {
  return Boolean(value) && typeof value === "object" && !Array.isArray(value);
}

function isString(value) {
  return typeof value === "string";
}

function isStringArray(value) {
  return Array.isArray(value) && value.every(isString);
}

function formatNumber(value) {
  return new Intl.NumberFormat("en-US").format(value);
}

function capitalize(value) {
  return value ? value.charAt(0).toUpperCase() + value.slice(1) : "";
}

function toCamelCase(value) {
  return value.replace(/-([a-z])/g, (_, letter) => letter.toUpperCase());
}

function escapeHtml(value) {
  return String(value ?? "")
    .replaceAll("&", "&amp;")
    .replaceAll("<", "&lt;")
    .replaceAll(">", "&gt;")
    .replaceAll('"', "&quot;")
    .replaceAll("'", "&#039;");
}
