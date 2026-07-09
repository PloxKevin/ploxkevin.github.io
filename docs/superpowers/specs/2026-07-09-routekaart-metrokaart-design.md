# Routekaart metrokaart + cohort-split — design

- **Date:** 2026-07-09
- **Status:** approved by user (scope, metro page, data rules, rollout — all four sections)
- **Repo surface:** `Routekaart/` in `ploxkevin.github.io` (GitHub Pages, push = deploy)
- **Predecessor spec:** `2026-07-09-routekaart-redesign-design.md` (DDOTT restyle, deployed)

## Context & sources

Agora (Buurtcollege Agora Maas en Peel) mandates a **metrokaart** format for 26/27
routekaarts (decoded from `Routekaart_format_2627.docx` + vakcoaches deck): one metro line
per vak/niveau in a self-chosen color spanning the cohort's two years, official symbols
(open circle = inflexibel PTA, dashed circle = flexibel PTA, filled dot = datapunt,
circle+pill = dubbel inzetbaar), PTA labels below / datapunt labels above the line
(slanted), legend bottom-right, line name bottom-left, and the footnote mechanism for
flexibility. The official **PTA NSK1 TL 2028 (overgangsversie)** defines cohort 2026–2028:
all five SE-toetsen in leerjaar 3 (P1–P4), leerjaar 4 = CE-voorbereiding, CE voorjaar
2028, plus an indicative K→A–F mapping (concept-programma v2, april 2026). Flexibiliteit
classification approved by the user after codex + web analysis: **NSK1-2 ↔ NSK1-3 are the
flexibele ster-paar; NSK1-1/4/5 inflexibel; no dubbel-inzetbaar pills** (sectie decides
later). The live site currently tells a single blended GT3+GT4 story; the mei-2027 CE
belongs to the current GT4 cohort (2025–2027) only.

## Canonical station data (single source of truth for all surfaces)

| # | Station | Periode | Vorm | Herkansbaar | Weging | Flex | Page | Nieuw progr. (indicatief) |
|---|---|---|---|---|---|---|---|---|
| NSK1-1 | Praktische opdracht — onderzoeks- en ontwerpvaardigheden | Lj3 · P1 | P | nee | 20% | inflexibel | `skills.html#po3` | Dom. E (E1, E2) · C · F |
| NSK1-2 | Licht en beeld | Lj3 · P2 | S | ja | 20% | **flexibel*** | `k7.html` | B5 (eindterm 15, oog) · C |
| NSK1-3 | Bouw van de materie | Lj3 · P2 | S/M | ja | 20% | **flexibel*** | `k10.html` | B3 · A |
| NSK1-4 | Straling en stralingsbescherming | Lj3 · P3 | S | ja | 20% | inflexibel | `k11.html` | B3 · C |
| NSK1-5 | Het weer | Lj3 · P4 | S | ja | 20% | inflexibel | `k12.html` | B5 (eindterm 16, systeem aarde) · D2 |
| — | Centraal Examen (terminus) | voorjaar 2028 | CE | — | 50% eindcijfer | — | `exam.html` | huidig programma K1–K12 |

Footnote, verbatim from the official format (must appear on every surface that shows a
ster): `*PTA-onderdelen met * kunnen in willekeurige volgorde worden afgerond. De
inlevermaand wordt dan gewisseld met een ander PTA-onderdeel.`

**Honesty rules:** period labels only — never invented months. Every label element gets a
`data-maand=""` attribute reserved for later single-line fills. Footer note on the metro
page: `Gebaseerd op PTA NSK1 vmbo-TL 2028 (overgangsversie)`. No links to Teams-internal
resources. CE 2028 is "voorjaar 2028" until an official rooster exists.

## 1. New page: `Routekaart/routekaart.html`

Standard site chrome (topbar with `← Routekaart` chip, footer). Eyebrow
`Cohort 2026–2028 · VMBO-TL · PTA 2028`; h1 `Metrokaart natuurkunde (NSK1)`; one intro
paragraph (student-facing: what the kaart shows, ster-uitleg, datapunten komen erbij).

**The SVG metrokaart** (inline, no JS):
- Container `div.metro-scroll` with `overflow-x: auto`; SVG `viewBox="0 0 1200 430"`,
  `min-width: 900px` so mobile scrolls horizontally instead of shrinking to mush.
- Line: `--accent` `#ff6b17`, `stroke-width: 6`, `stroke-linejoin/linecap: round`. Route:
  leerjaar-3 horizontal segment (y=310) carrying all five stations → **knik** (45° up)
  at the schooljaar boundary → leerjaar-4 horizontal segment (y=190) with **no stations**,
  labeled `Leerjaar 4 · 2027–2028 · CE-voorbereiding (K4–K9, V1, V2)` above the segment
  in muted text → terminus at the right end.
- Stations (official symbol grammar, all stroke `#ff6b17`, fill `--surface`):
  - inflexibel: circle `r=13`, `stroke-width: 4`
  - flexibel: same circle with `stroke-dasharray: 7 5`
  - terminus (CE): circle `r=16`, `stroke-width: 5` + inner filled dot `r=5`
  - datapunt (for later use): filled circle `r=5`, on the line between stations
- Jaargrens: thin vertical hairline `#dddddd` through the knik + small muted caption
  `zomer 2027`.
- **Station labels below the line**, slanted (`transform="rotate(-45 …)"`, text-anchor
  end), Space Grotesk 13px: first line ink `*NSK1-2 · Licht en beeld` (ster only on 2/3),
  second line muted `periode 2 · S · 20%`. Each station's whole group is wrapped in
  `<a href="…">` (SVG links) to its page.
- **Datapunt slots above the line**: shipped empty. An HTML comment block directly above
  the SVG documents the exact copy-paste template (one `<g class="metro-datapunt">`
  per datapunt: dot on the line + slanted label above), with one fully worked commented-out
  example (`<!-- voorbeeld: Feedbackmoment practicumverslag, tussen NSK1-1 en NSK1-2 -->`).
  This block is the teacher's edit surface.
- **Legend** bottom-right inside the SVG: the five official symbols (incl. the two
  dubbel-inzetbaar pill variants, marked `nog niet in gebruik` in muted text) with 12px
  labels. **Lijnnaam** bottom-left: orange line swatch + `NSK1 — natuurkunde`.
- Accessibility: `<svg role="img" aria-labelledby>` with `<title>` "Metrokaart NSK1
  cohort 2026–2028; tabel hieronder bevat dezelfde informatie". The table below is the
  canonical accessible representation.

**Below the SVG:** the full PTA table from the canonical data (columns: code, inhoud,
periode, vorm, herkansbaar, weging, aansluiting nieuw programma) as a normal DDOTT table,
followed by the ster-footnote, the SE-regels paragraph (SE volledig afgesloten eind lj3;
eindcijfer = gewogen gemiddelde, 1 decimaal), and the PTA-version footer note.

**CSS additions to `style.css`** (tokenized, appended as a `/* ---- Metrokaart ---- */`
block): `.metro-scroll`, `.metro-svg text` sizing/families, `.metro-note`, legend text
styles. No changes to existing rules.

## 2. `index.html`: two cohort lanes

Intro paragraph rewritten (two cohorts named; both lanes explained in one sentence each;
chip links unchanged). Quick-nav line gains `Metrokaart 2026–2028`. Then:

- **Lane 1** — `section-label`: `GT4 · Cohort 2025–2027 — leerjaar 4 · CE-voorbereiding`.
  Content: the three existing periode lists (K5/K9d1, K6/K8/K9d2, K4) and the existing
  orange CE-banner (27 mei 2027) — rows unchanged, only regrouped under this label.
- **Lane 2** — `section-label`: `GT3 · Cohort 2026–2028 — leerjaar 3 · 100% schoolexamen`.
  New `domain-list` from the canonical data, PO first:
  `NSK1-1 · Praktische opdracht → skills.html#po3 · tag "P1 · PO · 20%"`,
  `*NSK1-2 · Licht en beeld → k7.html · tag "P2 · S · 20%"`,
  `*NSK1-3 · Bouw van de Materie → k10.html · tag "P2 · S/M · 20%"`,
  `NSK1-4 · Straling → k11.html · tag "P3 · S · 20%"`,
  `NSK1-5 · Het Weer → k12.html · tag "P4 · S · 20%"`.
  Directly under the list: a second orange banner-link to `routekaart.html`
  (`Metrokaart cohort 2026–2028 · alle stations op één lijn` / `Bekijk de kaart →`)
  and the ster-footnote as a `note-muted` line.
- The doorlopende-vaardigheden note and footer stay.

The old single `Jaar 3 (GT3)` list (K7-first, PO-last, no periods) is **replaced** by
Lane 2. K-codes remain visible on the domain pages themselves; the index rows lead with
NSK1-codes (name column keeps the domain name students know).

## 3. Domain-page and exam-page corrections

- `k7.html`: eyebrow → `Jaar 3 · Schoolexamen · NSK1-2 · periode 2 · weegt 20%`; table
  row `20% (OND2)` → `20% (NSK1-2 · herkansbaar)`.
- `k10.html`: eyebrow gains `NSK1-3 · periode 2`; fix its Basisinformatie period claim
  ("periode 2-3" → `P2`) and any OND-label analog.
- `k11.html`: eyebrow gains `NSK1-4 · periode 3`; fix period claims to P3.
- `k12.html`: eyebrow gains `NSK1-5 · periode 4`; fix "typisch periode 1" → P4.
- `skills.html`: in the `#po3` section, add one info line: PO = `NSK1-1 · P1 · praktische
  opdracht met verslag · niet herkansbaar · 20%`.
- All five also get, in their Basisinformatie/weging area, the cohort qualifier
  `cohort 2026–2028 (PTA 2028)` so current-GT4 readers aren't misled.
- `exam.html`: eyebrow re-scoped to `Jaar 4 · 50% van het eindcijfer · per cohort
  hieronder`; the Examendetails info-box becomes two blocks:
  `Cohort 2025–2027 (huidig leerjaar 4)` with the existing verified 27-mei-2027 facts, and
  `Cohort 2026–2028` with: CE voorjaar 2028 (datum volgt via examenblad), SE volledig
  afgesloten in leerjaar 3 (2026-2027), verwijzing + link naar `routekaart.html`.

Implementation-time rule: locate exact current strings with grep before editing; the five
files may have small wording variants (only `k7.html` was read end-to-end this session).

## 4. Error handling & degradation

- No JS anywhere; SVG is static. Fonts blocked → system fallbacks (SVG `text` uses the
  same `--font-ui` stack).
- Screen readers: table is canonical; SVG announced via role/title only.
- Print: `.metro-scroll` prints at natural width (may clip on A4 portrait) — the table
  prints fully; acceptable. Add `.metro-scroll { overflow: visible }` in the print block.
- Old links unaffected: no file renames, no anchor changes; only additions and in-place
  label corrections.

## 5. Verification & rollout

- Extend the battery: link check must pass with `routekaart.html` included (its SVG `<a>`
  hrefs and the new index/exam links resolve); stale-string grep unchanged; new check:
  the ster-footnote appears verbatim on index + routekaart.html.
- **Codex format-compliance review** (user's standing instruction): after the page is
  built, codex reviews the rendered HTML against the format doc's rules (symbols, label
  positions, legend, footnote, honesty rules) before the user review gate.
- Subagent-driven execution with per-task review; local server user review; **push =
  deploy only on explicit user go**; Agora working-copy mirror refreshed after approval.

## Out of scope

Dubbel-inzetbaar pills (sectie decision pending); month labels (no source data);
datapunt content (teacher fills the template later); other vakken/niveaus/cohorten;
Teams structure; restructuring domain pages around A–F; updating `main.tex`.
