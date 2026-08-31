(function exposeCompletionImport(globalScope) {
  function normalizeStatus(value) {
    return String(value ?? "").trim().toLowerCase();
  }

  const OPERATIONAL_TASK_TEMPLATES = new Set([
    "elimination",
    "exit the location",
    "find and transfer",
  ]);

  function questNameMetadata(value) {
    const inputName = String(value ?? "").trim();
    const kordTagged = /^\s*\[\s*kord\s+breach\s*\]/i.test(inputName);
    const seasonPvpTagged = /\[\s*season\s+pvp\s*\]\s*$/i.test(inputName);
    const displayName = inputName
      .replace(/^\s*\[\s*kord\s+breach\s*\]\s*/i, "")
      .replace(/\s*\[\s*season\s+pvp\s*\]\s*$/i, "")
      .trim();

    return {
      inputName,
      displayName,
      datasetHint: kordTagged ? "storyline" : seasonPvpTagged ? "regular" : null,
      kordTagged,
      seasonPvpTagged,
    };
  }

  function normalizeQuestName(value) {
    return questNameMetadata(value).displayName
      .normalize("NFKD")
      .replace(/[\u2010-\u2015\u2212]/g, "-")
      .replace(/[\u2018\u2019\u02bc]/g, "'")
      .replace(/\u2026/g, "...")
      .toLowerCase()
      .replace(/&/g, " and ")
      .replace(/[^a-z0-9]+/g, " ")
      .trim()
      .replace(/\s+/g, " ");
  }

  function parseQuestStatusSections(text) {
    const sections = {
      active: [],
      completed: [],
      foundSections: { active: false, completed: false },
    };
    if (typeof text !== "string") return sections;

    let currentSection = null;
    let inFence = false;
    for (const rawLine of text.replace(/^\uFEFF/, "").split(/\r?\n/)) {
      const trimmed = rawLine.trim();
      if (/^(```|~~~)/.test(trimmed)) {
        inFence = !inFence;
        continue;
      }
      if (inFence) continue;

      const statusHeading = trimmed.match(
        /^(?:#{1,6}\s*)?(active|completed)(?:\s+quests?)?(?:\s*\(\s*\d+\s*\))?\s*:?\s*$/i,
      );
      if (statusHeading) {
        currentSection = statusHeading[1].toLowerCase();
        sections.foundSections[currentSection] = true;
        continue;
      }
      if (/^#{1,6}\s+/.test(trimmed)) {
        currentSection = null;
        continue;
      }
      if (!currentSection || !trimmed || /^(?:---+|___+|\*\*\*+)$/.test(trimmed)) continue;

      const listItem = rawLine.match(/^\s*(?:[-+*]|\d+[.)])\s+(?:\[[ xX]\]\s*)?(.+?)\s*$/);
      const plainItem = rawLine.match(/^\s*(?:\[[ xX]\]\s*)?([^#].*?)\s*$/);
      const item = (listItem?.[1] || plainItem?.[1] || "")
        .replace(/^\*\*(.+)\*\*$/, "$1")
        .replace(/^__(.+)__$/, "$1")
        .replace(/^`(.+)`$/, "$1")
        .trim();
      if (item) sections[currentSection].push(item);
    }

    return sections;
  }

  function questCatalogEntries(regularTasks, storylineQuests) {
    const regular = Array.isArray(regularTasks) ? regularTasks : regularTasks?.tasks || [];
    const storyline = Array.isArray(storylineQuests)
      ? storylineQuests
      : storylineQuests?.quests || [];
    return [
      ...regular
        .filter((task) => task && typeof task.id === "string" && typeof task.name === "string")
        .map((task) => ({
          dataset: "regular",
          id: task.id,
          name: task.name,
          trader: task.traderName || task.trader || null,
        })),
      ...storyline
        .filter((task) => task && typeof task.id === "string" && typeof task.name === "string")
        .map((task) => ({
          dataset: "storyline",
          id: task.id,
          name: task.name,
          trader: task.traderName || task.trader || null,
        })),
    ];
  }

  function classifyQuestStatusName(value, catalogEntries) {
    const metadata = questNameMetadata(value);
    const normalizedName = normalizeQuestName(metadata.displayName);
    const base = {
      inputName: metadata.inputName,
      displayName: metadata.displayName,
      normalizedName,
      datasetHint: metadata.datasetHint,
    };

    if (OPERATIONAL_TASK_TEMPLATES.has(normalizedName)) {
      return { ...base, kind: "operational", matchType: null, matches: [] };
    }

    const eligible = (catalogEntries || []).filter(
      (entry) => !metadata.datasetHint || entry.dataset === metadata.datasetHint,
    );
    const exactMatches = eligible.filter((entry) => entry.name === metadata.inputName);
    const strippedExactMatches = eligible.filter((entry) => entry.name === metadata.displayName);
    const normalizedMatches = eligible.filter(
      (entry) => normalizeQuestName(entry.name) === normalizedName,
    );
    const matches = exactMatches.length
      ? exactMatches
      : strippedExactMatches.length
        ? strippedExactMatches
        : normalizedMatches;
    const matchType = exactMatches.length
      ? "exact"
      : strippedExactMatches.length
        ? "tag-normalized"
        : normalizedMatches.length
          ? "normalized"
          : null;

    if (matches.length > 1) {
      return { ...base, kind: "ambiguous", matchType, matches };
    }
    if (matches.length === 1) {
      return { ...base, kind: "matched", matchType, matches };
    }
    if (metadata.seasonPvpTagged) {
      return { ...base, kind: "season-pvp-unmatched", matchType: null, matches: [] };
    }
    return { ...base, kind: "unmatched", matchType: null, matches: [] };
  }

  function uniqueMatchedIds(entries, dataset) {
    return [...new Set(entries
      .filter((entry) => entry.kind === "matched" && entry.matches[0]?.dataset === dataset)
      .map((entry) => entry.matches[0].id))];
  }

  function matchQuestStatusName(value, regularTasks = [], storylineQuests = []) {
    return classifyQuestStatusName(
      value,
      questCatalogEntries(regularTasks, storylineQuests),
    );
  }

  function parseQuestStatusText(text, regularTasks = [], storylineQuests = []) {
    const sections = parseQuestStatusSections(text);
    const catalog = questCatalogEntries(regularTasks, storylineQuests);
    const active = sections.active.map((name) => ({
      status: "active",
      ...classifyQuestStatusName(name, catalog),
    }));
    const completed = sections.completed.map((name) => ({
      status: "completed",
      ...classifyQuestStatusName(name, catalog),
    }));
    const entries = [...active, ...completed];
    const regularActiveIds = uniqueMatchedIds(active, "regular");
    const regularCompletedIds = uniqueMatchedIds(completed, "regular");
    const storylineActiveIds = uniqueMatchedIds(active, "storyline");
    const storylineCompletedIds = uniqueMatchedIds(completed, "storyline");
    const operational = entries.filter((entry) => entry.kind === "operational");
    const seasonPvpUnmatched = entries.filter((entry) => entry.kind === "season-pvp-unmatched");
    const unmatched = entries.filter((entry) => entry.kind === "unmatched");
    const ambiguous = entries.filter((entry) => entry.kind === "ambiguous");
    const normalizedMatches = entries.filter(
      (entry) => entry.kind === "matched" && entry.matchType !== "exact",
    );
    const matched = entries.filter((entry) => entry.kind === "matched");
    const matchKey = (entry) => `${entry.matches[0]?.dataset}:${entry.matches[0]?.id}`;
    const activeByKey = new Map(active
      .filter((entry) => entry.kind === "matched")
      .map((entry) => [matchKey(entry), entry]));
    const completedByKey = new Map(completed
      .filter((entry) => entry.kind === "matched")
      .map((entry) => [matchKey(entry), entry]));
    const conflicts = [...activeByKey.keys()]
      .filter((key) => completedByKey.has(key))
      .map((key) => ({
        dataset: activeByKey.get(key).matches[0].dataset,
        id: activeByKey.get(key).matches[0].id,
        active: activeByKey.get(key),
        completed: completedByKey.get(key),
      }));

    return {
      format: "observed-quest-status-list",
      observedSnapshot: true,
      sections,
      entries: { active, completed },
      regularActiveIds,
      regularCompletedIds,
      storylineActiveIds,
      storylineCompletedIds,
      // Import-compatible aliases deliberately contain only explicitly observed regular completions.
      explicitIds: regularCompletedIds,
      inferredIds: [],
      completedIds: regularCompletedIds,
      unknownIds: [],
      operational,
      seasonPvpUnmatched,
      unmatched,
      ambiguous,
      conflicts,
      counts: {
        active: active.length,
        completed: completed.length,
        total: entries.length,
        matched: matched.length,
        exact: matched.length - normalizedMatches.length,
        normalized: normalizedMatches.length,
        fuzzy: 0,
        ambiguous: ambiguous.length,
        operational: operational.length,
        seasonPvpUnmatched: seasonPvpUnmatched.length,
        unmatched: unmatched.length,
      },
      playerLevel: null,
      faction: null,
      reputation: null,
      updatedAt: null,
      profileOnly: false,
      replaceExisting: sections.foundSections.completed,
    };
  }

  function idsFromStatusRecord(record) {
    if (!record || typeof record !== "object" || Array.isArray(record)) return [];
    return Object.entries(record)
      .filter(([, value]) => {
        if (value === true) return true;
        if (typeof value === "string") {
          return ["complete", "completed", "success", "done"].includes(normalizeStatus(value));
        }
        if (value && typeof value === "object") {
          const status = value.status ?? value.state ?? value.completed;
          return status === true || ["complete", "completed", "success", "done"].includes(normalizeStatus(status));
        }
        return false;
      })
      .map(([id]) => id);
  }

  function getCandidateIds(payload) {
    if (Array.isArray(payload)) return { ids: payload, format: "task-id-list" };
    if (!payload || typeof payload !== "object") return { ids: [], format: "unknown" };

    const candidates = [
      [
        payload.type === "kord-breach-profile-backup" ? payload.regular?.completed : null,
        "unified-profile-backup",
      ],
      [payload.completed_ids, "original-raid-optimizer"],
      [payload.progress?.completedQuests, "kappa-tracker-export"],
      [payload.completedQuests, "completed-quests-export"],
      [payload.completed, payload.type === "kord-breach-regular-progress" ? "tracker-backup" : "completed-array"],
    ];

    for (const [value, format] of candidates) {
      if (Array.isArray(value)) return { ids: value, format };
    }

    for (const [value, format] of [
      [payload.tasksCompletions, "tarkov-tracker-status-map"],
      [payload.taskCompletions, "task-status-map"],
      [payload.tasks, "task-status-map"],
    ]) {
      const ids = idsFromStatusRecord(value);
      if (ids.length) return { ids, format };
    }

    return { ids: [], format: payload.aid && payload.info ? "tarkov-dev-profile" : "unknown" };
  }

  function inferPrerequisites(explicitIds, taskById) {
    const completed = new Set(explicitIds);
    const inferred = new Set();
    const queue = [...completed];

    while (queue.length) {
      const task = taskById.get(queue.pop());
      if (!task) continue;

      for (const requirement of task.taskRequirements || []) {
        const statuses = (Array.isArray(requirement.status) ? requirement.status : [requirement.status])
          .filter(Boolean)
          .map(normalizeStatus);
        const requiresCompletion =
          statuses.length === 0 ||
          (statuses.length === 1 && statuses[0] === "complete");
        if (!requiresCompletion || completed.has(requirement.taskId) || !taskById.has(requirement.taskId)) {
          continue;
        }

        completed.add(requirement.taskId);
        inferred.add(requirement.taskId);
        queue.push(requirement.taskId);
      }
    }

    return { completed, inferred };
  }

  function normalizeFaction(value) {
    const faction = normalizeStatus(value);
    if (faction === "usec") return "USEC";
    if (faction === "bear") return "BEAR";
    return null;
  }

  function levelFromExperience(experience, playerLevels) {
    const totalExperience = Number(experience);
    if (!Number.isFinite(totalExperience) || totalExperience < 0 || !playerLevels?.length) return null;
    let spent = 0;
    let level = 1;

    for (const entry of [...playerLevels].sort((a, b) => a.level - b.level)) {
      if (spent + Number(entry.exp || 0) > totalExperience) break;
      spent += Number(entry.exp || 0);
      level = Number(entry.level) || level;
    }
    return level;
  }

  function validDate(value) {
    if (!value) return null;
    const date = new Date(typeof value === "number" ? value : String(value));
    return Number.isNaN(date.getTime()) ? null : date.toISOString();
  }

  function parseCompletionPayload(payload, tasks, playerLevels = []) {
    const taskById = new Map(tasks.map((task) => [task.id, task]));
    const knownIds = new Set(taskById.keys());
    const { ids: rawIds, format } = getCandidateIds(payload);
    const uniqueIds = [...new Set(rawIds.filter((id) => typeof id === "string"))];
    const explicitIds = uniqueIds.filter((id) => knownIds.has(id));
    const unknownIds = uniqueIds.filter((id) => !knownIds.has(id));
    const { completed, inferred } = inferPrerequisites(explicitIds, taskById);
    const profile =
      payload?.type === "kord-breach-profile-backup" && payload.regular
        ? payload.regular
        : payload;
    const directPlayerLevel = Number(
      profile?.playerLevel ?? profile?.progress?.pmcLevel ?? profile?.level ?? profile?.pmcLevel,
    );
    const playerLevel =
      Number.isFinite(directPlayerLevel) && directPlayerLevel > 0
        ? directPlayerLevel
        : levelFromExperience(profile?.info?.experience, playerLevels);
    const faction = normalizeFaction(profile?.faction ?? profile?.info?.side ?? profile?.side);
    const updatedValue = payload?.updated ?? payload?.updatedAt ?? payload?.exportedAt;
    const updatedAt = validDate(updatedValue);

    return {
      format,
      explicitIds,
      inferredIds: [...inferred],
      completedIds: [...completed],
      unknownIds,
      playerLevel,
      faction,
      reputation:
        ["kord-breach-regular-progress", "kord-breach-profile-backup"].includes(payload?.type) &&
        profile?.reputation &&
        typeof profile.reputation === "object"
          ? profile.reputation
          : null,
      updatedAt,
      profileOnly:
        ["tarkov-dev-profile", "unified-profile-backup"].includes(format) &&
        explicitIds.length === 0,
      replaceExisting: ["kord-breach-regular-progress", "kord-breach-profile-backup"].includes(
        payload?.type,
      ),
    };
  }

  globalScope.KordCompletionImport = {
    classifyQuestStatusName,
    getCandidateIds,
    inferPrerequisites,
    levelFromExperience,
    matchQuestStatusName,
    normalizeQuestName,
    parseCompletionPayload,
    parseQuestStatusSections,
    parseQuestStatusText,
  };
})(typeof window !== "undefined" ? window : globalThis);
