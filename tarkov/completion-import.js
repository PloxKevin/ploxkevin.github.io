(function exposeCompletionImport(globalScope) {
  function normalizeStatus(value) {
    return String(value ?? "").trim().toLowerCase();
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
        const statuses = Array.isArray(requirement.status) ? requirement.status : [requirement.status];
        const requiresCompletion =
          statuses.length === 0 ||
          (statuses.includes("complete") && !statuses.includes("active"));
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
    const directPlayerLevel = Number(
      payload?.playerLevel ?? payload?.progress?.pmcLevel ?? payload?.level ?? payload?.pmcLevel,
    );
    const playerLevel =
      Number.isFinite(directPlayerLevel) && directPlayerLevel > 0
        ? directPlayerLevel
        : levelFromExperience(payload?.info?.experience, playerLevels);
    const faction = normalizeFaction(payload?.faction ?? payload?.info?.side ?? payload?.side);
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
        payload?.type === "kord-breach-regular-progress" && payload.reputation && typeof payload.reputation === "object"
          ? payload.reputation
          : null,
      updatedAt,
      profileOnly: format === "tarkov-dev-profile" && explicitIds.length === 0,
      replaceExisting: payload?.type === "kord-breach-regular-progress",
    };
  }

  globalScope.KordCompletionImport = {
    getCandidateIds,
    inferPrerequisites,
    levelFromExperience,
    parseCompletionPayload,
  };
})(typeof window !== "undefined" ? window : globalThis);
