# Routekaart 2026–2027 redesign — design

- **Date:** 2026-07-09
- **Status:** approved by user (visual system, architecture, content, cleanup — all four sections)
- **Deployed source:** `Routekaart/` in this repo (`ploxkevin.github.io`, branch `main` = GitHub Pages)
- **Working copy / archive:** `~/Dropbox/Agora/Routekaart/` (extra sources: `sections/*.tex`, README, PTA PDF)
- **Live URL:** https://ploxkevin.github.io/Routekaart/index.html

## Context

The Routekaart is a Dutch VMBO-TL natuurkunde curriculum site: `index.html` plus 9 domain
pages (`k4`–`k12`), `formulas`, `skills`, `exam`, `learning_hierarchy` — 15 pages sharing
one `style.css`. Problems: the 2020 gradient-card look is dated; every page says
"Schooljaar 2025-2026"; every page loads the **compromised `polyfill.io` CDN** (domain
began serving malware in 2024 — must be removed regardless of styling); white text sits on
saturated gradients with contrast as low as ~1.4:1.

Style source: `~/StyleGuides/22-d-d-o-t-t-type-foundry/` (clean-brutalist "document, not
landing page"). Chosen by the user from three mockup candidates (19-primer, 25-reapi,
22-ddott) rendered with real Routekaart content. Per the StyleGuides ethos we reuse the
**system** (tokens, roles, discipline), not the pixels; the library's hard rule is
preserved: dependency-free static HTML/CSS, no build step, no JS framework.

## Visual system

All values become CSS custom properties in the rewritten `style.css`, taken from
`22-d-d-o-t-t-type-foundry/design-tokens.json`:

| Token | Value | Role |
|---|---|---|
| `--page-bg` | `#ecedef` | full-bleed page field; also link-chip color |
| `--surface` | `#ffffff` | topbar, footer, cards, lists |
| `--text` | `#686868` | body (4.76:1 on page-bg — AA) |
| `--ink` | `#111111` | headings, emphasis, K-codes (16.12:1 — AAA) |
| `--accent` | `#ff6b17` | **scarce**: CE-exam banner, primary buttons, 3px left edge of warning/exam-tip notes |
| `--accent-dark` | `#d74300` | hover state |
| `--muted` | `#adadae` | meta labels ("SE · 20%"), hairlines-on-white |
| `--line` | `#dddddd` | borders/dividers |

- **Type:** Space Grotesk (Google Fonts, 400/500/700, `display=swap`, preconnect) as the
  single UI voice; Space Mono (400/700) only for formulas. Fallback `Arial, Helvetica,
  sans-serif`. Scale: h1 40px/1.1 w400, h2 32px, h3 28px (all `#111`, weight 400), body
  16px / **fixed 21px line-height** / 0.09px letter-spacing, small 13px/17px, eyebrow
  16px uppercase w700.
- **Surfaces:** `border-radius: 0` everywhere; 1px `#ddd` borders; shadow only
  `0 1px 2px rgba(17,17,17,.06)`. No gradients anywhere.
- **Links:** marker-highlight chips — `background:#ecedef; padding:1px 4px; color:#111`
  on white surfaces (inverted: white chip on the gray page field), background fades on
  hover over `0.3s ease-out`. Nav links `#686868 → #111`.
- **Buttons:** flat orange, **black** label (7.37:1), `13px/35px`, height 40px,
  padding `0 15px`, radius 0, `all .15s ease-in-out`. Focus ring
  `0 0 0 3px rgb(255 107 23 / 28%)`.
- **Never white text on orange** (2.85:1 — fails). Light theme only; no dark mode
  (faithful to source; document/print ethos). Motion budget: hover transitions only.
- **Print:** column is inherently print-friendly; keep a small `@media print` block
  (hide topbar nav, black text).

## Page architecture

- **Layout:** narrow centered document column, `max-width: 800px`, on the full-bleed
  gray field. White topbar and footer bars sized to the column.
- **Shared chrome on all 15 pages:**
  - Topbar: site name (`#111`, w500) left; right: `Formules · Vaardigheden · Examen`
    (13px). Subpages get a `← Routekaart` chip instead of/next to the nav.
  - Footer: `VMBO-TL Natuurkunde Curriculum 2026–2027` | `Gemaakt voor Agora`.
- **`index.html`** is restructured (its markup is navigation chrome): uppercase eyebrow
  `SCHOOLJAAR 2026–2027 · VMBO-TL · GT3 & GT4`, h1, intro paragraph with chip links,
  quick-nav line (Leerpiramide · Vaardigheden K1–K3 · 13 kernformules · Examen-info),
  then per-period **white list blocks**: rows of `K-code (bold #111) + naam + right-aligned
  muted role label` ("SE · 20%", "CE · deel 1"). Jaar 3 one list; Jaar 4 three lists
  (P1 sep–nov: K5, K9 deel 1 · P2 nov–feb: K6, K8, K9 deel 2 · P3 feb–mei: K4). After P3:
  the one loud element — **orange CE banner** "Centraal Examen — mei 2027 · 50% van het
  eindcijfer" linking to `exam.html`. Closing muted note about doorlopende vaardigheden
  K1–K3. **Legend section is deleted** (roles are labeled inline). The old "Welkom" card
  text merges into the intro paragraph.
- **Domain pages `k4`–`k12`** keep their content markup; existing class names
  (`.card`, `.formula-box`, `.info-box*`, `table`, `.back-link`) are restyled by the new
  `style.css`: cards → white bordered blocks; `.formula-box` → white block with Space
  Mono formula + muted explanation; `.info-warning`/`.info-danger` → white note card
  with 3px orange left border; `.info-primary`/`.info-success` → same card with 3px
  `#111`/`#ddd` left border (orange stays exam-only); tables → white, 1px `#ddd` rules,
  `#111` w700 header row on white (no more blue fill). Page top gets the eyebrow meta
  line (jaar · SE/CE · weging/periode). Next/previous domain links become the orange
  button + a chip link back to the kaart.
- **Support pages:** `formulas.html` — formula cards in Space Mono; `skills.html`,
  `exam.html` — standard document treatment; `learning_hierarchy.html` — the rainbow
  pyramid becomes a typographic level list (numbered white rows, level number bold
  `#111`, description muted; size/indentation gradation, no colors).
- **Emoji are stripped** from headings/cards sitewide (🧠🛠️📐📝⚠️ etc.).
- **Anchor IDs are preserved** (`k9.html#deel1`, `#deel2`, `skills.html#po3`) so existing
  deep links keep working.

## Content updates (2026–2027)

- Replace every `2025-2026` with `2026-2027` (all 15 pages: header/eyebrow + footers).
- CE references: "mei 2027" (index banner, exam.html).
- **Verification step (blocking, during implementation):** fetch examenblad.nl for
  **nask1 GL/TL 2027** — CE datum (tijdvak 1), tijdsduur, toegestane hulpmiddelen,
  syllabus/wijzigingen t.o.v. 2026 — and correct `exam.html` facts where they differ.
  If examenblad is unreachable, mark the affected facts with the year only (no invented
  dates) and tell the user what could not be verified.
- Domain/period structure, weights (4 × 20% + PO 20%), and 50/50 SE/CE split unchanged.

## Cleanup

- Remove the `polyfill.io` `<script>` from **all** pages (compromised CDN).
- MathJax 3 from jsdelivr stays **only** on pages that actually contain TeX math
  (determine via `grep -l '\\\\(\|\\$\\$'` during implementation); remove the tag elsewhere.
- `git rm` LaTeX build artifacts from the deployed dir: `main.aux`, `main.log`, `main.out`.
- `main.tex` / `main.pdf` stay untouched (unlinked printable; still says 2025-2026 — accepted).
- Add `.superpowers/` to the repo `.gitignore`. The file already has unrelated local
  modifications — inspect the diff and commit only the added line's hunk if separable,
  otherwise stage the whole file only after confirming the other edits are benign.
- After user approval of the result: mirror the updated `*.html` + `style.css` to
  `~/Dropbox/Agora/Routekaart/` so both copies agree.

## Error handling & degradation

- Fonts offline/blocked → system fallback stack renders acceptably (document layout
  doesn't depend on exact metrics).
- No JS → pages fully readable; only MathJax typesetting degrades to raw TeX on the
  math pages. Accepted for this site.
- Old bookmarks/deep links → preserved anchors and unchanged filenames.

## Verification

- `python -m http.server` in `Routekaart/`; click through all 15 pages.
- `grep -rn "2025-2026\|polyfill" Routekaart/ --include="*.html" --include="*.css"` → zero hits.
- Internal link check: every `href` target file/anchor exists (scripted grep pass).
- MathJax renders on the retained math pages (browser check).
- Print preview sanity on `index.html` and one domain page.
- User reviews the served site before any commit; **push = deploy**, only on explicit go.

## Out of scope

- Updating `main.tex`/`main.pdf` content; other sections of `ploxkevin.github.io`;
  the Agora-copy LaTeX sources (`sections/*.tex`); dark mode; any JS interactivity.
