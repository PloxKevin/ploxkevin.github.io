# KORD BREACH regular quest and reputation research

Research snapshot: **30 August 2026**  
Mode: **PvP Season (`pvp-season`)**  
Patch: **1.1.0.0**

## What the regular quests change

The KORD BREACH seasonal storyline and the regular side-task pool are related but not the same progression system.

- The KORD BREACH storyline begins after the story chapter **Tour**, then follows its own prerequisite chain.
- Regular quests are the main source of trader reputation. Reputation plus PMC level determines each trader's Loyalty Level (LL).
- Most regular side tasks are assigned to an LL band and are released in small groups. Reaching a new LL exposes that tier's opening group; completing tasks at that tier advances hidden counters that expose later groups.
- Patch 1.1.0.0 removed trader sales volume from LL requirements. Spending money no longer helps reach the next LL.
- Valuable exception chains still use direct quest prerequisites and may award no reputation.

This means regular tasks do **not** need to be cleared before starting every KORD BREACH task. They do determine how much of the regular quest pool and trader inventory is open alongside the seasonal storyline.

## Current seasonal trader thresholds

These values come from the current `pvp-season/traders` snapshot.

| Trader | LL2 | LL3 | LL4 |
|---|---:|---:|---:|
| Prapor | Level 6 / 0.70 rep | Level 21 / 2.70 rep | Level 36 / 7.90 rep |
| Therapist | Level 5 / 0.60 rep | Level 18 / 2.10 rep | Level 37 / 5.80 rep |
| Skier | Level 7 / 0.60 rep | Level 22 / 2.10 rep | Level 38 / 5.80 rep |
| Peacekeeper | Level 8 / 0.50 rep | Level 19 / 2.20 rep | Level 37 / 6.00 rep |
| Mechanic | Level 12 / 0.60 rep | Level 26 / 2.30 rep | Level 40 / 7.60 rep |
| Ragman | Level 12 / 0.50 rep | Level 27 / 2.00 rep | Level 42 / 6.50 rep |
| Jaeger | Level 9 / 0.60 rep | Level 17 / 2.10 rep | Level 33 / 7.30 rep |
| Ref | Level 15 / 0.25 rep | Level 25 / 0.50 rep | Level 35 / 1.20 rep |
| Fence | 6.00 rep for the next loyalty state | — | — |

## Rep bands and task groups

The season data clusters ordinary reputation tasks into four clear reward bands:

| Progression band | Typical standing reward |
|---|---:|
| LL1 | +0.10 |
| LL2 | +0.25 |
| LL3 | +0.75 |
| LL4 | +1.50 |

The feed exposes 164 tasks with hidden global-variable gates. Those gates use thresholds such as 1, 3 and 5 completed tasks within a tier. The exact thresholds vary by trader and LL.

Important limitation: the public data exposes each counter's ID and required value, but not the server-side rule that increments it. It also omits an explicit LL requirement on the unchained opening tasks in a trader's pool. The frontend maps counters and unchained opening pools to LL bands using the standing rewards above, then estimates progress from the tasks marked complete. These cards are labeled **Est. LL** rather than presenting the inference as a verified requirement. Direct task-chain exceptions are kept out of this inferred opening-pool rule. Check the in-game task list and counter if the estimate differs.

This distinction fixes an earlier modeling error: nine unchained +0.25 tasks were labeled LL2 but treated as available at LL1. They are now consistently modeled as estimated LL2 opening-pool tasks in both the All Quests board and raid planner. **Loyalty Buyout** is not included because its failed-branch prerequisite makes it a direct chain exception, consistent with both the seasonal data and its Wiki route.

## Dataset audit

- 491 raw task definitions in the seasonal-profile feed; 490 are shown in the tracker
- 481 distinct visible quest names; eight names have faction or alternative-route variants
- 198 tasks with direct quest prerequisites
- 164 tasks with hidden per-tier group gates
- 109 tasks with explicit trader requirements
- 9 unchained LL2 opening-pool gates inferred from the +0.25 seasonal reward band
- 336 tasks with at least one positive standing reward
- 1 task with a negative completion reward: **Choose Your Friends Wisely** gives **BTR Driver -0.30**

The snapshot contains enough total positive reputation to reach LL4 for the seven ordinary LL traders. Ref is different: the regular seasonal task feed only exposes a small amount of Ref standing, so Arena-linked progression remains relevant. Fence reputation is also influenced by Scav actions and extracts, not only quest rewards.

## Official Wiki chain cross-check

The 198 local task instances with direct prerequisites were compared by Wiki URL against the English Official Escape from Tarkov Wiki on **30 August 2026**. Duplicate in-game variants resolve to 192 unique Wiki pages.

- 135 Wiki pages publish a non-empty `Previous` relationship.
- 122 of those match the union of current seasonal prerequisites exactly.
- 57 linked quest pages leave `Previous` blank, so they cannot validate or contradict the game-data chain.
- 12 comparable pages differ. Collector also looks different mechanically because its infobox links to its own requirements section; that is a sentinel, not another quest.
- Across populated Wiki chains, 9 say **Accept**, 2 say **Fail**, 4 explicitly use **or**, and 18 include a delay.
- The current 491-task graph has 217 prerequisite edges, unique IDs, no missing targets, no self-edges and no strict-completion cycles.

The board continues to use the current `pvp-season` snapshot for availability. Patch 1.1.0.0 substantially reworked side-task progression, while many differing Wiki relationships were last substantively edited before that rework. Replacing the newer game data wholesale with those pages would risk restoring old chains. Instead, affected cards show a Wiki advisory and link to the page so the player can verify the live in-game route.

| Quest | Current seasonal data | Wiki `Previous` |
|---|---|---|
| Building Foundations | Resolve Swift Retribution | Swift Retribution **or** Inevitable Response |
| The Price of Independence | Battery Change + Discombobulate | Discombobulate |
| The Huntsman Path - Controller | The Survivalist Path - Tough Guy | The Huntsman Path - Forest Cleaning |
| The Survivalist Path - Cold Blooded | The Huntsman Path - Controller | The Survivalist Path - Wounded Beast |
| The Survivalist Path - Eagle-Owl | The Survivalist Path - Cold Blooded | The Survivalist Path - Tough Guy |
| The Survivalist Path - Unprotected but Dangerous | The Survivalist Path - Zhivchik | Acquaintance |
| The Survivalist Path - Wounded Beast | The Survivalist Path - Unprotected but Dangerous | The Survivalist Path - Zhivchik |
| Information Source | Knock-Knock | Getting Acquainted |
| Forge a Friendship | Swift Retribution + Natural Exchange | Hot Wheels + Natural Exchange |
| Another Shipping Delay | Natural Exchange + Inevitable Response | Fail Hot Wheels + Natural Exchange |
| The Higher They Fly | Accept or complete Building Foundations | Swift Retribution **or** Inevitable Response |
| A Healthy Alternative | Accept One Less Loose End | Overpopulation |

Two otherwise matching pages differ only in state: the Wiki says to **accept** the predecessor for The Tarkov Shooter - Part 2 and Simple Side Job, while the current seasonal feed requires completion. Six more Wiki pages show delays absent from the current feed: Hot Wheels - Let's Try Again (+24h), Hindsight 20/20 (+6h), Key Partner (+6h), Killer Argument (+6h), Route Deviation (+6h), and Thirsty - Secrets (+12–13h). These are displayed as Wiki timing advisories rather than enforced as availability gates. Sensory Analysis - Part 1 is a smaller difference: Wiki +30m versus the feed's 30–35m range.

The audit also found and corrected the feed's ambiguous `Immunity` link so the task now opens [`Immunity (quest)`](https://escapefromtarkov.fandom.com/wiki/Immunity_(quest)) rather than the character skill.

The feed also retains an older `The Tarkov Shooter - Part 5` definition (night-time Customs Scavs) alongside the current Sniper Scav version. Only the current version leads to Part 6 and matches the Wiki, so the legacy definition is kept in the research snapshot but hidden from both trackers. The two `The Huntsman Path - Administrator` definitions are labeled **BEAR / Reserve** and **USEC / Lighthouse** from the Wiki. Other duplicate names are shown as explicit alternative routes; marking one complete clears a completed sibling with the same name so route-only variants cannot inflate counters.

## Sources and refresh method

- [Official Patch 1.1.0.0 announcement](https://store.steampowered.com/news/posts/?enddate=1785796555&feed=steam_community_announcements)
- [Official developer explanation of the side-task rework](https://steamcommunity.com/app/3932890/discussions/1/588433186648965193/)
- [Tarkov.dev static endpoint catalog](https://json.tarkov.dev/endpoints)
- [Official Wiki quest index](https://escapefromtarkov.fandom.com/wiki/Quests)
- Live snapshot endpoints: `pvp-season/tasks`, `pvp-season/traders`, `pvp-season/maps`, plus their `_en` translation files

Refresh the machine-readable snapshot with:

```powershell
cd frontend
npm run refresh:data
```

Then run `npm test` to rebuild and verify the GitHub Pages output.

## Quest completion imports

The original `raid_optimizer.py` used two different sources:

- Tarkov.dev GraphQL supplied task definitions, IDs, maps and prerequisites.
- `obs-kappa-tracker.com/api/users/{username}` supplied completion IDs through `progress.completedQuests`, with `completed.txt` as its local fallback.

The current public Tarkov.dev player snapshot (`players.tarkov.dev/pvp-season/{aid}.json`) exposes profile statistics, experience and faction, but it does not expose a completed-quest list. It also omits browser CORS headers, which means a dependency-free GitHub Pages site cannot fetch it directly without a separate proxy.

The frontend therefore accepts completion JSON locally and matches imported IDs against the current seasonal task snapshot. Supported formats include the original optimizer's `my_progress.json`, its cached `completed.txt`, a tracker `completedQuests` export, task status maps, plain ID arrays and this frontend's own backups. Required completed prerequisites are inferred using the same conservative rule as the original optimizer: only prerequisites whose status explicitly requires `complete`, not merely `active`.
