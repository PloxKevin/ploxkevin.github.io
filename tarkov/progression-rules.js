(function installProgressionRules(root) {
  const CURATED_MANUAL_REQUIREMENTS = Object.freeze({
    "69c26c07683c9831020018c7": [{
      label: "Complete the Icebreaker scientist-intercom and damaged-door interactions",
      source: "wiki-requirement",
    }],
    "69ce1cfb298a6529b30d712b": [{
      label: "Hand the Boreas compartment C-1 hard drives to Mechanic",
      source: "wiki-requirement",
    }],
    "69ce1de03e15cd80bd06f6c9": [{
      label: "Hand the Boreas compartment C-1 hard drives to Mechanic",
      source: "wiki-requirement",
    }],
    "69ce21e990144e437802b1e0": [{
      label: "Hand the Boreas compartment C-1 hard drives to Mechanic",
      source: "wiki-requirement",
    }],
    "69ce204c8702b378f9091e4b": [{
      label: "Hand the Boreas compartment C-1 hard drives to Mechanic",
      source: "wiki-requirement",
    }],
    "67af4c1d8c9482eca103e477": [{
      label: "Complete Profit Retention or Get a Foothold",
      source: "wiki-prerequisite",
    }],
    "675c15fbf7da9792a4059871": [{
      label: "Accept Easy Money - Part 2",
      source: "wiki-prerequisite",
      satisfiedByExternalNames: ["Easy Money - Part 2"],
    }],
  });

  function normalizeQuestName(value) {
    return String(value || "")
      .replace(/^\s*\[\s*kord\s+breach\s*\]\s*/i, "")
      .replace(/\s*\[\s*season\s+pvp\s*\]\s*$/i, "")
      .normalize("NFKD")
      .replace(/[\u2018\u2019\u02bc]/g, "'")
      .toLowerCase()
      .replace(/[^a-z0-9]+/g, " ")
      .trim();
  }

  function getCuratedManualRequirements(task) {
    return (CURATED_MANUAL_REQUIREMENTS[task?.id] || []).map((requirement) => ({ ...requirement }));
  }

  function curatedRequirementSatisfied(requirement, externalStatuses) {
    const accepted = (requirement?.satisfiedByExternalNames || []).map(normalizeQuestName);
    if (!accepted.length) return false;
    return (externalStatuses || []).some((entry) =>
      ["active", "completed"].includes(entry?.status) && accepted.includes(normalizeQuestName(entry.name)),
    );
  }

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
    getCuratedManualRequirements,
    getModeledLoyaltyGate,
    getSeasonPool,
    curatedRequirementSatisfied,
  });
})(typeof window === "undefined" ? globalThis : window);
