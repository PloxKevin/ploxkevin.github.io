(function installProgressionRules(root) {
  function normalizeTier(value) {
    const tier = Number(value);
    return Number.isInteger(tier) && tier >= 1 && tier <= 4 ? tier : null;
  }

  function explicitOwnTraderTier(task) {
    const tiers = (task?.traderRequirements || [])
      .filter((requirement) =>
        requirement.requirementType === "level" &&
        requirement.traderId === task.traderId &&
        [">=", ">", "=", "==", "==="].includes(requirement.compareMethod),
      )
      .map((requirement) => normalizeTier(requirement.value))
      .filter(Boolean);
    return tiers.length ? Math.max(...tiers) : null;
  }

  function getSeasonPool(task) {
    if (!task) return null;

    let tier = normalizeTier(task.seasonPoolTier);
    let source = task.seasonPoolTierSource || null;

    // Backward-compatible interpretation for snapshots generated before provenance was stored.
    if (!tier) {
      const explicitTier = explicitOwnTraderTier(task);
      if (explicitTier) {
        tier = explicitTier;
        source = "explicit-level";
      } else if ((task.globalRequirements || []).length && normalizeTier(task.progressionTier)) {
        tier = normalizeTier(task.progressionTier);
        source = "inferred-group";
      }
    }

    if (!tier) return null;
    const definitions = {
      "explicit-level": { kind: "requirement", estimated: false },
      "inferred-group": { kind: "task group", estimated: true },
      "inferred-opening": { kind: "opening pool", estimated: true },
    };
    const definition = definitions[source] || { kind: "task pool", estimated: true };
    return { tier, source, ...definition };
  }

  function getModeledLoyaltyGate(task) {
    const pool = getSeasonPool(task);
    return pool?.estimated ? pool : null;
  }

  function getCompactPoolLabel(task) {
    const pool = getSeasonPool(task);
    if (!pool) return "";
    if (pool.source === "explicit-level") return `LL${pool.tier} requirement`;
    if (pool.source === "inferred-group") return `Est. LL${pool.tier} group`;
    if (pool.source === "inferred-opening") return `Est. LL${pool.tier} opening`;
    return `Est. LL${pool.tier} pool`;
  }

  root.KordProgressionRules = Object.freeze({
    explicitOwnTraderTier,
    getCompactPoolLabel,
    getModeledLoyaltyGate,
    getSeasonPool,
  });
})(typeof window === "undefined" ? globalThis : window);
