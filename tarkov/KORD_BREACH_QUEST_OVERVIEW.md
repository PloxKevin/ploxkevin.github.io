# KORD BREACH Season 1 quest overview

Last verified: 30 August 2026  
Game patch: 1.1.0.0  
Mode: Seasonal PvP character only

This guide covers the documented KORD BREACH storyline, its parallel tasks, the late-game choice, requirements, objectives, items, maps, and rewards. The structured companion file is [kord_breach_quests.json](kord_breach_quests.json).

Seasonal task data is still changing. The values below use the current Escape from Tarkov Wiki pages as of the verification date. In particular, Sheep in Wolf's Clothing was reduced from 6 to 4 kills per map on 23 August; older guides still show 18 total kills.

## At a glance

- There are 17 documented quest entries.
- Final Stretch and Consequences of Our Decisions are mutually exclusive, so one character can complete at most 16 of the 17.
- Completing all available entries with either branch awards 365,000 base quest EXP and ₽3,588,000 before Intelligence Center bonuses, plus the listed item rewards.
- None of these quests is required for Kappa.
- The main starting gate is Tour completed plus Prapor Loyalty Level 2.
- Key to Understanding additionally requires player level 20.
- Consequences of Our Decisions and Digital Puzzle require Intelligence Center level 1.
- Reverse Gear has a 0-2 hour unlock delay.
- What's in the Bag? has a 1-2 hour unlock delay after Key to Understanding.
- Unanswered Calls, Riding the Wave, and Stay Clear of Blast Zone run alongside the main chain.

## Season rules that affect this route

- KORD BREACH uses a separate Seasonal Character and separate PvP progression.
- Insurance is unavailable.
- Black Division can be encountered on Ground Zero 21+, Shoreline, and Streets of Tarkov.
- Black Division replaces Raiders on The Lab.
- Transit out of The Lab is unavailable.
- Hideout crafts take half the usual time.
- Experience gain is increased by 25%.
- Hideout zones do not require Found in Raid status, but quest handovers still do whenever the objective explicitly says so.

## Quest dependency map

    Tour + Prapor LL2
      └─ Uninvited Guests - Part 1
           ├─ on acceptance: Unanswered Calls [parallel]
           └─ on acceptance: Uninvited Guests - Part 2
                └─ Cast the Net
                     └─ Know Your Enemy
                          └─ wait 0-2 h: Reverse Gear
                               ├─ Riding the Wave [parallel]
                               └─ Key to Understanding [level 20]
                                    └─ wait 1-2 h: What's in the Bag?
                                         └─ Forbidden Knowledge
                                              └─ Sheep in Wolf's Clothing
                                                   ├─ Final Stretch [Fence choice]
                                                   └─ Consequences of Our Decisions
                                                      [Mechanic choice; starts after
                                                       accepting Final Stretch]
                                                        └─ either choice completed:
                                                           Desperate Assault
                                                             ├─ on acceptance:
                                                             │  Stay Clear of Blast Zone
                                                             └─ on completion:
                                                                Break the Chain
                                                                  └─ Digital Puzzle

## Items to keep before they are requested

Do not burn rare Black Division gear on the first available handover. Some pieces overlap between multiple tasks.

| Item | Quantity | Found in Raid? | Used for |
|---|---:|:---:|---|
| Any accepted Black Division plate carrier | 5 | No | Know Your Enemy |
| Usable accepted Black Division plate carrier | 1 | No | Wear for Sheep in Wolf's Clothing |
| First Spear Siege-R Black Division carrier | 1 | Yes | Riding the Wave |
| Spiritus LV-119 Black Division V2 | 1 | Yes | Riding the Wave |
| Ferro FCPC V5 Black Division | 1 | Yes | Riding the Wave |
| Spiritus LV-119 Black Division V1 | 1 | Yes | Riding the Wave |
| Tasmanian Tiger Modular Pack 45 Plus MCB | 1 | Yes | Riding the Wave |
| Mystery Ranch 2 Day Assault Pack (Black) | 1 | Yes | Riding the Wave |
| Mystery Ranch NICE Frame Load Sling | 1 | Yes | Riding the Wave |
| Avon M53A1 gas mask | 1 | Yes | Riding the Wave |
| Gentex Ops-Core SOTR respirator | 1 | Yes | Riding the Wave |
| Gatorz Specter MILSPEC glasses | 1 | Yes | Riding the Wave |
| Black Division encryption keys | 1 | Yes | Key to Understanding |
| Briefcase with documents | 1 | Yes | What's in the Bag?; must come from Black Division outside The Lab |
| 14-4 KORD SSD | 3 | Yes | Forbidden Knowledge |
| Black Division rugged laptop | 1 | No | Digital Puzzle |
| WI-FI Camera | 6 | No | Cast the Net; buy from Mechanic LL1 |
| TP-200 TNT brick | 3 | No | Stay Clear of Blast Zone |

Accepted carriers for Know Your Enemy and Sheep in Wolf's Clothing:

- Ferro Concepts FCPC V5 Plate Carrier (Black Division)
- First Spear Siege-R Optimized M.A.S.S. Plate Carrier (Black Division)
- Spiritus Systems LV-119 Plate Carrier (Black Division V1)
- Spiritus Systems LV-119 Plate Carrier (Black Division V2)
- Spiritus Systems LV-119 Plate Carrier (MultiCam Black)

## Detailed quest guide

### 1. Uninvited Guests - Part 1

Trader: Prapor  
Map: Shoreline  
Requires: Tour completed, Prapor LL2, Seasonal mode  
Unlocks on acceptance: Uninvited Guests - Part 2 and Unanswered Calls

Objectives:

- Locate and obtain the case with military equipment.
- The case is at one of three locations: the SORDI tower shack, Weather Station second floor, or the Hydroelectric Power Station.
- The three investigation subtasks are optional.

Important:

- The case is a quest item and is lost on death.
- Part 2 becomes available when Part 1 is accepted, rather than after it is completed.

Rewards: 6,000 EXP; ₽18,000; RPK-16; three 6L23 magazines; one 120-round pack of 5.45x39 PP gs.

### 2. Uninvited Guests - Part 2

Trader: BTR Driver  
Maps: Shoreline, Woods, or Streets of Tarkov  
Requires: Uninvited Guests - Part 1 active, Seasonal mode  
Unlocks: Cast the Net

Objective:

- Hand the case with military equipment to the BTR Driver.

Important:

- The case remains a loss-on-death quest item.
- Because Part 2 activates with Part 1, a favorable Shoreline BTR route can avoid a separate transport raid.

Reward: 5,000 EXP.

### 3. Unanswered Calls

Trader: Therapist  
Map: Ground Zero  
Requires: Uninvited Guests - Part 1 active, Seasonal mode  
Type: Parallel task

Objectives, all in one raid:

- Stash Therapist's letter behind the reception desk on the second floor of the TerraGroup office.
- Extract through Nakatani Basement Stairs or Emercom Checkpoint.

Item: Therapist's message. Therapist resends it through messages after a death.

Rewards: 11,000 EXP; ₽180,000; two Grizzly kits; two CMS kits.

### 4. Cast the Net

Trader: Prapor  
Maps: Shoreline, Streets of Tarkov, Ground Zero  
Requires: Uninvited Guests - Part 2 completed, Seasonal mode  
Bring: six WI-FI Cameras, purchasable from Mechanic LL1  
Unlocks: Know Your Enemy

Objectives:

- Shoreline: Ural truck near the Hydroelectric Power Station.
- Shoreline: excavator near the smugglers' base.
- Streets: concrete mixer at the collapsed crane.
- Streets: bio toilet near Rodina cinema.
- Ground Zero: cargo truck cabin near Mira Ave.
- Ground Zero: yellow bus in the underground tunnel.

Minimum routing is one raid per map if both placements on that map are completed together.

Rewards: 11,000 EXP; ₽180,000; two Bottles of Fierce Hatchling moonshine.

### 5. Know Your Enemy

Trader: Prapor  
Requires: Cast the Net completed, Seasonal mode  
Unlocks: Reverse Gear after 0-2 hours

Objective:

- Hand over any five accepted Black Division plate carriers.

Found in Raid is not required. Preserve the exact FiR variants needed for Riding the Wave and retain one usable carrier for Sheep in Wolf's Clothing.

Rewards: 11,000 EXP; ₽180,000; five F-1 grenades; five RGD-5 grenades.

### 6. Reverse Gear

Trader: Prapor  
Maps: Shoreline, Streets of Tarkov, Ground Zero  
Requires: Know Your Enemy completed, 0-2 hour delay, Seasonal mode  
Unlocks: Key to Understanding and Riding the Wave

Objectives:

- Recover the six cameras from the same two locations per map used in Cast the Net.
- Hand all recovered cameras to Prapor.

The recovered cameras are quest items and must be brought out successfully. Plan one clean extraction from each map.

Rewards: 11,000 EXP; ₽180,000; two 6B23-2 Mountain Flora armors; one Briefcase with documents.

### 7. Key to Understanding

Trader: Fence  
Requires: Reverse Gear completed, player level 20, Seasonal mode  
Unlocks: What's in the Bag? after 1-2 hours

Objective:

- Find and hand over one found-in-raid Black Division encryption keys item.

The keys are a non-guaranteed Black Division drop.

Rewards: 30,000 EXP; ₽300,000; two TerraGroup Labs access keycards.

### 8. Riding the Wave

Trader: Ragman  
Requires: Reverse Gear completed, Seasonal mode  
Type: Parallel collection task

Hand over one found-in-raid copy of each:

- First Spear Siege-R Optimized M.A.S.S. Plate Carrier (Black Division)
- Spiritus Systems LV-119 Plate Carrier (Black Division V2)
- Ferro Concepts FCPC V5 Plate Carrier (Black Division)
- Spiritus Systems LV-119 Plate Carrier (Black Division V1)
- Tasmanian Tiger Modular Pack 45 Plus (MultiCam Black)
- Mystery Ranch 2 Day Assault Pack (Black)
- Mystery Ranch NICE Frame Load Sling
- Avon M53A1 gas mask
- Gentex Ops-Core SOTR respirator
- Gatorz Specter MILSPEC ballistic glasses

Rewards: 30,000 EXP; ₽300,000; one NPP KlASS Bagariy (EMR); three Crye Precision AVS (Ranger Green).

### 9. What's in the Bag?

Trader: Fence  
Requires: Key to Understanding completed, 1-2 hour delay, Seasonal mode  
Unlocks: Forbidden Knowledge

Objective:

- Find and hand over one found-in-raid Briefcase with documents.

The required briefcase drops from Black Division outside The Lab. A briefcase obtained as a quest reward does not satisfy the FiR requirement.

Rewards: 30,000 EXP; ₽300,000; one Intelligence folder; one Topographic survey maps.

Data note: the current Wiki infobox and quest chain place this after Key to Understanding. One Requirements bullet says the delay follows Know Your Enemy; this guide follows the dependency graph.

### 10. Forbidden Knowledge

Trader: Fence  
Requires: What's in the Bag? completed, Seasonal mode  
Unlocks: Sheep in Wolf's Clothing

Objective:

- Find and hand over three found-in-raid 14-4 KORD SSDs.

These are specific seasonal SSDs looted from Black Division, not ordinary SSDs.

Rewards: 30,000 EXP; ₽300,000; three Peltor TEP-300 tactical earplugs (Coyote Brown).

### 11. Sheep in Wolf's Clothing

Trader: Fence  
Maps: Shoreline, Streets of Tarkov, Ground Zero  
Requires: Forbidden Knowledge completed, Seasonal mode  
Unlocks: the Final Stretch branch choice

Objectives:

- Kill four Black Division operatives on Shoreline while wearing an accepted Black Division carrier.
- Kill four on Streets while wearing an accepted carrier.
- Kill four on Ground Zero while wearing an accepted carrier.

Current total: 12 kills. Older pages showing six per map are outdated.

The Ground Zero objective uses the level 21+ version of the map, so the chain cannot be finished at player level 20 even though Key to Understanding unlocks at level 20.

Rewards: 30,000 EXP; ₽300,000; one Money case; one QBZ-191; QBZ-191 purchase unlocked at Skier LL3.

### 12A. Final Stretch — Fence choice

Trader: Fence  
Map: Streets of Tarkov  
Requires: Sheep in Wolf's Clothing completed, Seasonal mode  
Mutually exclusive with: Consequences of Our Decisions  
Unlocks: Desperate Assault

Objectives:

- Find the laptop in Fence's stash at the small ventilation chimney behind the diner on Nikitskaya Street.
- Extract and hand the laptop to Fence.

This is the faster choice because it has no Hideout processing step.

Rewards: 35,000 EXP; ₽300,000; one RB-BK marked key; one Briefcase with documents; Profit Over Principles achievement.

### 12B. Consequences of Our Decisions — Mechanic choice

Trader: Mechanic  
Map: Streets of Tarkov plus Hideout  
Requires: Final Stretch accepted, Intelligence Center level 1, Seasonal mode  
Mutually exclusive with: Final Stretch  
Unlocks: Desperate Assault

Objectives:

- Find the same laptop used by Final Stretch.
- Craft Data from Fence's laptop at Intelligence Center level 1.
- Read the data in the off-raid quest inventory.
- Hand the laptop to Mechanic.

Rewards: 35,000 EXP; ₽300,000; five Electric drills; three Military COFDM transmitters; five Cyclon batteries; five Toolsets; one Briefcase with documents; Profit Over Principles achievement.

Both branch choices currently reconnect at Desperate Assault. Completing one fails the other.

### 13. Desperate Assault

Trader: Mechanic  
Map: The Lab  
Requires: either Final Stretch or Consequences of Our Decisions completed, Seasonal mode  
Unlocks on acceptance: Stay Clear of Blast Zone  
Unlocks on completion: Break the Chain

Objective:

- Eliminate 15 Black Division operatives in The Lab.

Rewards: 30,000 EXP; ₽300,000; one Weapon repair kit; one Body armor repair kit.

### 14. Stay Clear of Blast Zone

Trader: Jaeger  
Map: Shoreline  
Requires: Desperate Assault active, Seasonal mode  
Bring: three TP-200 TNT bricks  
Type: Parallel task

Objectives:

- Plant one TNT brick at each of the Health Resort's west, north, and east perimeter fence breaches.

Rewards: 30,000 EXP; ₽300,000; one HK G28; three 10-round G28 magazines; two 20-round packs of M62 Tracer.

### 15. Break the Chain

Trader: Mechanic  
Maps: Customs and Woods  
Requires: Desperate Assault completed, Seasonal mode  
Unlocks: Digital Puzzle

Shoot four transmitters:

- Customs: factory/boiler chimney near the unfinished construction site.
- Customs: power-line tower near Railroad to Military Base.
- Woods: top of Sniper Mountain.
- Woods: radio/cell tower near Scav Bunker.

Magnified optics make the devices easier to identify; climbing the structures is unnecessary.

Rewards: 30,000 EXP; ₽300,000; one FN SCAR-H FDE; three 20-round SCAR-H magazines; five 20-round packs of M80.

### 16. Digital Puzzle

Trader: Mechanic  
Maps: Black Division location plus Hideout  
Requires: Break the Chain completed, Intelligence Center level 1, Seasonal mode

Objectives:

- Obtain a Black Division rugged laptop.
- Decrypt it into Data from Black Division laptop at Intelligence Center level 1.
- Hand the data to Mechanic.

The Wiki currently marks the rugged laptop itself as not requiring FiR status.

Rewards: 35,000 EXP; ₽150,000; one T H I C C Weapon case; one T H I C C item case; one Briefcase with documents.

## Known Seasonal-mode task stubs

These pages exist but are not part of the usable route yet:

- Historical Perspectives: marked Seasonal mode, but the Wiki states it is not currently obtainable; trader, objectives, and rewards are unknown.
- Timeout: Mechanic, Seasonal mode, requires Scav karma +2; objective is to wait for Lightkeeper to contact Mechanic. The Wiki states it cannot currently be completed.

They are recorded in the JSON file but excluded from the 17-entry route and optimizer counts.

## Related task outside the KORD storyline

Fresh Stock is a Boreas-story Ragman task rather than a Seasonal-only KORD quest. It asks for five found-in-raid Black Division carriers after the Compartment C-1 hard-drive handover. Its accepted variants are the Ferro FCPC V5, Spiritus LV-119 V2, and Spiritus LV-119 MultiCam Black. During KORD BREACH, its reward changes to two black Rys-T helmets instead of the normal barter unlock. If you are also progressing Boreas, reserve another five FiR carriers for it.

## Recommended raid-planning priorities

1. Buy all six WI-FI Cameras before starting Cast the Net.
2. Keep every unique FiR Black Division equipment piece until Riding the Wave is satisfied.
3. Use non-FiR or duplicate carriers for Know Your Enemy.
4. Retain a serviceable accepted carrier for the 12 armored Black Division kills.
5. Farm the outside maps until you have the FiR briefcase; a Labs briefcase does not count for What's in the Bag?
6. Combine encryption-key, SSD, rugged-laptop, and Riding the Wave farming whenever possible.
7. Stock three TNT bricks before accepting Desperate Assault so the Jaeger side task is immediately runnable.
8. Choose the Fence branch for speed or the Mechanic branch for its crafting-material rewards; both lead to the same next quest.

## Sources and provenance

- Escape from Tarkov Wiki API: https://escapefromtarkov.fandom.com/api.php
- Current KORD BREACH ordering and map cross-check: https://www.tarkov101.com/kordbreach
- Branch and late-route cross-check: https://overgear.com/guides/eft/season-1-quests/
- tarkov.dev endpoint catalog: https://json.tarkov.dev/endpoints

The Wiki API was used because the current tarkov.dev pvp-season task feed did not contain the named KORD BREACH storyline at the time of verification. Exact game behavior takes precedence if a live hotfix changes an objective before these sources update.
