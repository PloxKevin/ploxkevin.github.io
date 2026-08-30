const STORAGE_KEYS = {
  completed: "kord-breach:completed",
  secured: "kord-breach:secured-loot",
  route: "kord-breach:route",
};

const state = {
  data: null,
  completed: new Set(readStoredArray(STORAGE_KEYS.completed)),
  secured: new Set(readStoredArray(STORAGE_KEYS.secured)),
  route: readStoredValue(STORAGE_KEYS.route, "fence"),
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
    hydrateFilterOptions();
    renderAll();
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
      document.querySelectorAll("[data-status]").forEach((item) => {
        item.classList.toggle("is-active", item === button);
      });
      renderQuests();
    });
  });

  document.querySelectorAll("[data-route]").forEach((button) => {
    button.addEventListener("click", () => {
      state.route = button.dataset.route;
      writeStoredValue(STORAGE_KEYS.route, state.route);
      document.querySelectorAll("[data-route]").forEach((item) => {
        item.classList.toggle("is-active", item === button);
      });
      renderAll();
      showToast(`${capitalize(state.route)} route selected`);
    });
  });

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

  document.querySelectorAll("[data-route]").forEach((button) => {
    button.classList.toggle("is-active", button.dataset.route === state.route);
  });
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
  const nextQuest = routeQuests.find((quest) => !state.completed.has(quest.id));

  dom.completedCount.textContent = completedCount;
  dom.routeCount.textContent = routeQuests.length;
  dom.progressPercent.textContent = `${percent}%`;
  dom.progressRing.style.setProperty("--progress", `${percent * 3.6}deg`);
  dom.nextQuest.textContent = nextQuest
    ? `Next: ${nextQuest.name}`
    : "Route complete. Good hunting.";
}

function renderLoot() {
  const loot = getPriorityLoot();
  const securedCount = loot.filter((item) => state.secured.has(item.name)).length;
  dom.lootCount.textContent = `${securedCount} / ${loot.length} secured`;

  dom.lootList.innerHTML = loot
    .map(
      (item) => `
        <label class="loot-item">
          <input
            type="checkbox"
            data-loot-name="${escapeHtml(item.name)}"
            ${state.secured.has(item.name) ? "checked" : ""}
          >
          <span class="check-box" aria-hidden="true"></span>
          <span class="loot-name">${escapeHtml(item.name)}</span>
          <span class="loot-qty">×${item.quantity}</span>
        </label>
      `,
    )
    .join("");
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
    .flatMap((quest) => quest.items || [])
    .filter((item) => item.found_in_raid)
    .forEach((item) => {
      const previous = loot.get(item.name);
      loot.set(item.name, {
        name: item.name,
        quantity: Math.max(item.quantity || 1, previous?.quantity || 0),
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
  const routeQuests = getRouteQuests();
  const visible = routeQuests.filter(matchesFilters);

  dom.questList.innerHTML = visible.map(renderQuestCard).join("");
  dom.resultCount.textContent = `${visible.length} of ${routeQuests.length} tasks`;
  dom.emptyState.hidden = visible.length > 0;
}

function matchesFilters(quest) {
  const complete = state.completed.has(quest.id);
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
  return true;
}

function renderQuestCard(quest) {
  const complete = state.completed.has(quest.id);
  const categoryLabel =
    quest.category === "parallel"
      ? "Parallel"
      : quest.category === "branch"
        ? `${capitalize(quest.branch || "")} branch`
        : "Main route";
  const prerequisites = renderPrerequisites(quest);
  const rewardLines = renderRewardLines(quest);

  return `
    <article class="quest-card ${complete ? "is-complete" : ""}" data-card-id="${escapeHtml(quest.id)}">
      <div class="quest-main">
        <div class="quest-number">${String(quest.order).padStart(2, "0")}</div>
        <div>
          <h3 class="quest-title">${escapeHtml(quest.name)}</h3>
          <div class="quest-meta">
            <span class="quest-trader">${escapeHtml(quest.trader)}</span>
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
          <button
            class="details-toggle"
            type="button"
            data-expand="${escapeHtml(quest.id)}"
            aria-expanded="false"
            aria-label="Show details for ${escapeHtml(quest.name)}"
          >Details</button>
        </div>
      </div>

      <div class="quest-details">
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
  const button = event.target.closest("[data-expand]");
  if (!button) {
    return;
  }

  const card = button.closest(".quest-card");
  const expanded = card.classList.toggle("is-expanded");
  button.setAttribute("aria-expanded", String(expanded));
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
    state.completed.add(quest.id);
    if (quest.mutually_exclusive_with) {
      const alternate = state.data.quests.find(
        (item) => item.name === quest.mutually_exclusive_with,
      );
      if (alternate) {
        state.completed.delete(alternate.id);
      }
    }
  } else {
    state.completed.delete(quest.id);
  }

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
  state.filters = { search: "", trader: "", map: "", status: "all" };
  dom.searchInput.value = "";
  dom.traderFilter.value = "";
  dom.mapFilter.value = "";
  document.querySelectorAll("[data-status]").forEach((button) => {
    button.classList.toggle("is-active", button.dataset.status === "all");
  });
  renderQuests();
}

function exportProgress() {
  const backup = {
    version: 1,
    exportedAt: new Date().toISOString(),
    completed: [...state.completed],
    securedLoot: [...state.secured],
    route: state.route,
  };
  const blob = new Blob([JSON.stringify(backup, null, 2)], {
    type: "application/json",
  });
  const url = URL.createObjectURL(blob);
  const anchor = document.createElement("a");
  anchor.href = url;
  anchor.download = "kord-breach-progress.json";
  anchor.click();
  URL.revokeObjectURL(url);
  showToast("Progress backup exported");
}

async function importProgress(event) {
  const [file] = event.target.files;
  event.target.value = "";
  if (!file) {
    return;
  }

  try {
    const backup = JSON.parse(await file.text());
    if (!Array.isArray(backup.completed) || !Array.isArray(backup.securedLoot)) {
      throw new Error("Invalid backup structure");
    }

    const validIds = new Set(state.data.quests.map((quest) => quest.id));
    state.completed = new Set(backup.completed.filter((id) => validIds.has(id)));
    state.secured = new Set(backup.securedLoot.filter((name) => typeof name === "string"));
    state.route = backup.route === "mechanic" ? "mechanic" : "fence";

    writeStoredArray(STORAGE_KEYS.completed, [...state.completed]);
    writeStoredArray(STORAGE_KEYS.secured, [...state.secured]);
    writeStoredValue(STORAGE_KEYS.route, state.route);
    document.querySelectorAll("[data-route]").forEach((button) => {
      button.classList.toggle("is-active", button.dataset.route === state.route);
    });
    renderAll();
    showToast("Progress backup imported");
  } catch (error) {
    showToast("That file is not a valid KORD BREACH backup");
  }
}

function resetProgress() {
  const confirmed = window.confirm(
    "Reset all quest progress, loot checks and the selected branch on this device?",
  );
  if (!confirmed) {
    return;
  }

  state.completed.clear();
  state.secured.clear();
  state.route = "fence";
  Object.values(STORAGE_KEYS).forEach((key) => {
    try {
      localStorage.removeItem(key);
    } catch {
      // Browser storage can be unavailable in hardened modes.
    }
  });
  document.querySelectorAll("[data-route]").forEach((button) => {
    button.classList.toggle("is-active", button.dataset.route === "fence");
  });
  renderAll();
  showToast("Local progress reset");
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
