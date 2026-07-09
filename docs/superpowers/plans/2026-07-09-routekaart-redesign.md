# Routekaart 2026–2027 Redesign Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Restyle all 14 pages of the VMBO-TL natuurkunde Routekaart in the DDOTT clean-brutalist document style, bump the schooljaar to 2026–2027 with the verified CE date, and remove the compromised polyfill.io script.

**Architecture:** One rewritten shared `style.css` (DDOTT tokens as CSS custom properties) restyles existing class names; `index.html` is rewritten wholesale; the 13 subpages get a mechanical chrome swap (head/nav/header/footer) via a Python transform script plus targeted manual edits. Static HTML/CSS only — no build step, no JS framework (MathJax stays on the 8 pages that use TeX).

**Tech Stack:** Plain HTML/CSS, Space Grotesk + Space Mono via Google Fonts, MathJax 3 (jsdelivr), Python 3 (transform/check scripts only, not shipped).

## Global Constraints

- Working dir: `~/Dropbox/ploxkevin.github.io/Routekaart/` (deployed via GitHub Pages from branch `main`). **NEVER `git push` in this plan** — push = deploy; it happens only on the user's explicit go, after their review.
- Spec: `docs/superpowers/specs/2026-07-09-routekaart-redesign-design.md` (repo-relative).
- Tokens (exact hexes, from `~/StyleGuides/22-d-d-o-t-t-type-foundry/design-tokens.json`): page `#ecedef`, surface `#ffffff`, text `#686868`, ink `#111111`, accent `#ff6b17`, accent-dark `#d74300`, muted `#adadae`, line `#dddddd`.
- Contrast rules: body `#686868` only on `#ecedef` (4.76:1) or `#ffffff` (5.57:1); **black labels on orange, never white**; orange text on gray only for large/UI.
- `border-radius: 0` everywhere; no gradients; no box shadows except `0 1px 2px rgba(17,17,17,.06)`.
- Fonts: `'Space Grotesk', Arial, Helvetica, sans-serif` (UI), `'Space Mono', monospace` (formula labels only). Google Fonts with `display=swap` + preconnect.
- Year string everywhere: `2026-2027` (typographic `2026–2027` only in visible copy where noted). CE date (verified 2026-07-09 on examenblad.nl/2027/examenrooster): **donderdag 27 mei 2027, 13:30–15:30, tijdvak 1**.
- MathJax stays ONLY on: `exam.html`, `formulas.html`, `k4.html`, `k5.html`, `k6.html`, `k8.html`, `k9.html`, `k11.html`. Removed from: `index.html`, `k7.html`, `k10.html`, `k12.html`, `skills.html`, `learning_hierarchy.html`. polyfill.io removed from ALL.
- Preserve anchor ids: `k9.html#deel1`, `k9.html#deel2`, `skills.html#k1/#k2/#k3/#po3`, per-page section ids (`#leerdoelen` etc.).
- All UI copy in Dutch.
- Helper scripts live in the scratchpad (`/tmp/claude-1000/-home-oxrexkevin/d766e6e1-1b21-4842-aa02-5853a01a85c1/scratchpad`), are NOT committed.
- Commit after every task; end commit messages with:
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` and
  `Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV`
- Intermediate commits may leave subpages visually plain (old chrome + new CSS). Acceptable: nothing is deployed until the final push.

---

### Task 1: Repo groundwork (artifacts + .gitignore)

**Files:**
- Delete: `Routekaart/main.aux`, `Routekaart/main.log`, `Routekaart/main.out`
- Modify: `.gitignore` (repo root — append one line)

**Interfaces:**
- Consumes: nothing.
- Produces: clean repo state later tasks commit onto. `.gitignore` covers `.superpowers/` so companion mockups never get committed.

- [ ] **Step 1: Verify the .gitignore modification is whitespace-only churn**

Run: `cd ~/Dropbox/ploxkevin.github.io && git diff --ignore-all-space --stat .gitignore`
Expected: empty output (confirms content-identical modulo whitespace; already confirmed 2026-07-09).

- [ ] **Step 2: Remove LaTeX build artifacts and append gitignore entry**

```bash
cd ~/Dropbox/ploxkevin.github.io
git rm --quiet Routekaart/main.aux Routekaart/main.log Routekaart/main.out
printf '\n# Superpowers brainstorm companion sessions\n.superpowers/\n' >> .gitignore
```

- [ ] **Step 3: Verify state**

Run: `git status --short | grep -E "gitignore|main\." && ls Routekaart/ | grep -c "^main"`
Expected: `M .gitignore`, three `D  Routekaart/main.*` lines, and `2` (only `main.tex`, `main.pdf` remain).

- [ ] **Step 4: Commit**

```bash
git add .gitignore
git commit -m "Remove LaTeX build artifacts from deployed dir, gitignore .superpowers/

.gitignore diff is whitespace normalization plus the new entry.

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 2: Rewrite style.css (the DDOTT token system)

**Files:**
- Rewrite: `Routekaart/style.css` (full replacement, content below)

**Interfaces:**
- Consumes: nothing.
- Produces: class contract used by every later task — `.container`, `.topbar`, `.topbar-nav`, `.chip`, `header`/`.eyebrow`, `.card`, `.formula-box`, `.info-box` (+`info-success|warning|danger|primary`), `table`, `.back-link`, `.btn`, `.bottom-nav`, `.domain-list`, `.domain-row` (+ child `.code`, `.name`, `.tag`), `.exam-banner`, `.hierarchy-level`, `.note-muted`, `footer`.

- [ ] **Step 1: Replace the entire file with:**

```css
/* Routekaart — DDOTT clean-brutalist document system
   Tokens: StyleGuides/22-d-d-o-t-t-type-foundry (2026-07-09 redesign) */

* { margin: 0; padding: 0; box-sizing: border-box; }

:root {
    --page-bg: #ecedef;
    --surface: #ffffff;
    --text: #686868;
    --ink: #111111;
    --accent: #ff6b17;
    --accent-dark: #d74300;
    --muted: #adadae;
    --line: #dddddd;
    --shadow-pop: 0 1px 2px rgba(17, 17, 17, 0.06);
    --focus-ring: 0 0 0 3px rgb(255 107 23 / 28%);
    --font-ui: 'Space Grotesk', Arial, Helvetica, sans-serif;
    --font-mono: 'Space Mono', ui-monospace, Menlo, Consolas, monospace;
}

html { background: var(--page-bg); }

body {
    font-family: var(--font-ui);
    font-size: 16px;
    line-height: 21px;
    letter-spacing: 0.09px;
    color: var(--text);
    background: var(--page-bg);
    padding: 20px 15px 40px;
}

.container { max-width: 800px; margin: 0 auto; }

/* ---- Chrome ---- */
.topbar {
    background: var(--surface);
    padding: 8px 15px;
    margin-bottom: 24px;
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-wrap: wrap;
    gap: 4px 12px;
    box-shadow: var(--shadow-pop);
}

.topbar-title { color: var(--ink); font-weight: 500; text-decoration: none; font-size: 15px; }
.topbar-nav { display: flex; gap: 14px; align-items: center; flex-wrap: wrap; }
.topbar-nav a { color: var(--text); text-decoration: none; font-size: 13.5px; line-height: 24px; transition: color 0.15s ease-in-out; }
.topbar-nav a:hover { color: var(--ink); }

footer {
    background: var(--surface);
    margin-top: 32px;
    padding: 9px 15px;
    font-size: 13px;
    line-height: 17px;
    display: flex;
    justify-content: space-between;
    flex-wrap: wrap;
    gap: 4px 12px;
}

/* ---- Type ---- */
header { margin: 0 0 18px; }

.eyebrow {
    text-transform: uppercase;
    font-weight: 700;
    font-size: 13px;
    letter-spacing: 0.03em;
    color: var(--ink);
    margin-bottom: 10px;
}

h1 { color: var(--ink); font-weight: 400; font-size: 40px; line-height: 1.1; margin-bottom: 12px; }
h2 { color: var(--ink); font-weight: 400; font-size: 24px; line-height: 1.2; margin-bottom: 12px; }
h3 { color: var(--ink); font-weight: 400; font-size: 18px; line-height: 1.25; margin: 16px 0 8px; }

p { margin-bottom: 14px; }
ul, ol { margin: 0 0 14px 22px; }
li { margin-bottom: 6px; }
li > ul, li > ol { margin-top: 6px; margin-bottom: 0; }
strong { color: var(--ink); font-weight: 700; }
em { color: var(--ink); }
small { font-size: 13px; }

/* Marker-highlight chip links (the DDOTT signature: highlight fades OUT on hover) */
a { color: var(--ink); }
.card a, .info-box a, .formula-box a, p a, li a, td a {
    background: var(--page-bg);
    padding: 1px 4px;
    color: var(--ink);
    text-decoration: none;
    transition: background-color 0.3s ease-out;
}
.card a:hover, .info-box a:hover, .formula-box a:hover, p a:hover, li a:hover, td a:hover {
    background: var(--surface);
}
a.chip {
    background: var(--surface);
    padding: 1px 6px;
    color: var(--ink);
    text-decoration: none;
    font-size: 13.5px;
    transition: background-color 0.3s ease-out;
}
a.chip:hover { background: var(--page-bg); }
.topbar a.chip { background: var(--page-bg); }
.topbar a.chip:hover { background: var(--surface); outline: 1px solid var(--line); }

a:focus-visible, .btn:focus-visible, .back-link:focus-visible { outline: none; box-shadow: var(--focus-ring); }

/* ---- Surfaces ---- */
.card {
    background: var(--surface);
    border: 1px solid var(--line);
    border-radius: 0;
    padding: 20px;
    margin-bottom: 20px;
    box-shadow: var(--shadow-pop);
}
.card > h2:first-child { margin-top: 0; }

.formula-box {
    background: var(--surface);
    border: 1px solid var(--line);
    border-radius: 0;
    padding: 14px 16px;
    margin: 14px 0;
}
.formula-box h3 { margin-top: 0; font-family: var(--font-mono); font-size: 15px; }
.formula-box ul { margin-bottom: 0; }
.card .formula-box { border-left: 3px solid var(--ink); }

.info-box {
    background: var(--surface);
    border: 1px solid var(--line);
    border-radius: 0;
    padding: 12px 15px;
    margin: 14px 0;
    font-size: 14.5px;
}
.info-box ul, .info-box p:last-child { margin-bottom: 0; }
.info-warning, .info-danger { border-left: 3px solid var(--accent); }
.info-primary { border-left: 3px solid var(--ink); }
.info-success { border-left: 3px solid var(--line); }

/* ---- Tables ---- */
table { width: 100%; border-collapse: collapse; margin: 14px 0; background: var(--surface); font-size: 14.5px; }
th, td { padding: 9px 12px; text-align: left; border-bottom: 1px solid var(--line); }
th { color: var(--ink); font-weight: 700; border-bottom: 2px solid var(--ink); background: var(--surface); }
tr:last-child td { border-bottom: 0; }

/* ---- Buttons ---- */
.btn, .back-link {
    display: inline-block;
    background: var(--accent);
    border: 1px solid var(--accent);
    border-radius: 0;
    color: #000000;
    font-family: var(--font-ui);
    font-size: 13px;
    line-height: 35px;
    height: 37px;
    padding: 0 15px;
    text-decoration: none;
    transition: all 0.15s ease-in-out;
    margin: 6px 0;
}
.btn:hover, .back-link:hover { background: var(--accent-dark); border-color: var(--accent-dark); }
.bottom-nav { display: flex; align-items: center; gap: 14px; flex-wrap: wrap; margin: 24px 0 0; }

/* ---- Index: domain lists ---- */
.section-label {
    text-transform: uppercase;
    font-weight: 700;
    font-size: 13px;
    letter-spacing: 0.02em;
    color: var(--ink);
    margin: 22px 0 8px;
}
.section-label small { color: var(--muted); font-weight: 400; text-transform: none; letter-spacing: 0; }

.domain-list { background: var(--surface); border: 1px solid var(--line); box-shadow: var(--shadow-pop); }
.domain-row {
    display: flex;
    gap: 12px;
    align-items: baseline;
    padding: 10px 15px;
    border-bottom: 1px solid var(--line);
    color: var(--text);
    font-size: 15px;
    text-decoration: none;
    transition: background-color 0.3s ease-out;
}
.domain-row:last-child { border-bottom: 0; }
.domain-row:hover { background: var(--page-bg); }
.domain-row .code { color: var(--ink); font-weight: 700; min-width: 44px; }
.domain-row .name { color: var(--ink); }
.domain-row .tag { margin-left: auto; font-size: 13px; color: var(--muted); white-space: nowrap; }

.exam-banner {
    display: flex;
    justify-content: space-between;
    align-items: center;
    flex-wrap: wrap;
    gap: 4px 12px;
    background: var(--accent);
    border: 1px solid var(--accent);
    color: #000000;
    padding: 12px 15px;
    margin: 22px 0 14px;
    font-size: 15px;
    text-decoration: none;
    transition: all 0.15s ease-in-out;
}
.exam-banner:hover { background: var(--accent-dark); border-color: var(--accent-dark); }
.exam-banner strong { color: #000000; }
.exam-banner .go { font-size: 13.5px; }

.note-muted { font-size: 13px; color: var(--muted); margin: 0; }

/* ---- Leerpiramide (learning_hierarchy.html) ---- */
.hierarchy-level {
    background: var(--surface);
    border: 1px solid var(--line);
    border-left: 3px solid var(--ink);
    padding: 12px 15px;
    margin: 0 0 10px;
}
.hierarchy-level h3 { margin: 0 0 4px; }
.hierarchy-level p { margin: 0; font-size: 14.5px; }
.hierarchy-level.level-5 { border-left-color: var(--accent); }
.hierarchy-level.level-0 { border-left-color: var(--line); }
.hierarchy-level.level-0 h3, .hierarchy-level.level-0 p { color: var(--muted); }

/* ---- Responsive ---- */
@media (max-width: 620px) {
    body { padding: 12px 10px 32px; }
    h1 { font-size: 30px; }
    h2 { font-size: 21px; }
    .domain-row { flex-wrap: wrap; }
    .domain-row .tag { margin-left: 56px; }
}

/* ---- Print ---- */
@media print {
    html, body { background: #ffffff; }
    .topbar-nav, .bottom-nav, .back-link { display: none; }
    body { color: #000000; }
    .card, .domain-list, .info-box, .formula-box { box-shadow: none; }
    .exam-banner { background: #ffffff; border: 2px solid #000000; color: #000000; }
}
```

- [ ] **Step 2: Sanity-render a subpage against the new CSS**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart && python -m http.server 8021 &
sleep 1 && curl -s http://localhost:8021/style.css | head -5
```
Expected: the new token comment header. Open `http://localhost:8021/k7.html` mentally/in browser: cards are white/bordered, tables restyled; old `<nav>`/`<header>` render plain (unstyled) — accepted intermediate state per Global Constraints.

- [ ] **Step 3: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io
git add Routekaart/style.css
git commit -m "Rewrite Routekaart stylesheet with DDOTT document token system

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 3: Rewrite index.html

**Files:**
- Rewrite: `Routekaart/index.html` (full replacement, content below)

**Interfaces:**
- Consumes: Task 2 classes (`.topbar`, `.domain-list`, `.domain-row`, `.exam-banner`, `.section-label`, `.note-muted`, `.chip`).
- Produces: link targets unchanged (`k*.html`, `formulas.html`, `skills.html#po3`, `exam.html`, `learning_hierarchy.html`, `k9.html#deel1`, `k9.html#deel2`) — later tasks must keep these files/anchors alive.

- [ ] **Step 1: Replace the entire file with:**

```html
<!DOCTYPE html>
<html lang="nl">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>VMBO-TL Natuurkunde Routekaart GT3 & GT4</title>
    <link rel="preconnect" href="https://fonts.googleapis.com">
    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>
    <link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;700&family=Space+Mono:wght@400;700&display=swap" rel="stylesheet">
    <link rel="stylesheet" href="style.css">
</head>
<body>
    <div class="container">
        <div class="topbar">
            <a class="topbar-title" href="index.html">Natuurkunde Routekaart</a>
            <nav class="topbar-nav">
                <a href="formulas.html">Formules</a>
                <a href="skills.html">Vaardigheden</a>
                <a href="exam.html">Examen</a>
            </nav>
        </div>

        <header>
            <div class="eyebrow">Schooljaar 2026–2027 · VMBO-TL · GT3 &amp; GT4</div>
            <h1>VMBO-TL Natuurkunde, jaar 3 &amp; 4</h1>
        </header>

        <p>
            Deze routekaart beschrijft het volledige natuurkundecurriculum. Jaar 3 telt
            <a href="exam.html">100% als schoolexamen</a>, jaar 4 bereidt voor op het
            <a href="exam.html">centraal examen van 27 mei 2027</a>. Het eindcijfer is
            50% SE + 50% CE. Klik op een domein voor leerdoelen, formules, practicum
            en typische examenvragen.
        </p>
        <p style="font-size: 13.5px;">
            Sneller navigeren: <a href="learning_hierarchy.html">Leerpiramide</a> ·
            <a href="skills.html">Vaardigheden K1–K3</a> ·
            <a href="formulas.html">13 kernformules</a> ·
            <a href="exam.html">Examen-info</a>
        </p>

        <div class="section-label">Jaar 3 (GT3) — 100% schoolexamen <small>· augustus–juni</small></div>
        <div class="domain-list">
            <a class="domain-row" href="k7.html"><span class="code">K7</span><span class="name">Licht &amp; Beeld</span><span class="tag">SE · 20%</span></a>
            <a class="domain-row" href="k10.html"><span class="code">K10</span><span class="name">Bouw van de Materie</span><span class="tag">SE · 20%</span></a>
            <a class="domain-row" href="k11.html"><span class="code">K11</span><span class="name">Straling en Stralingsbescherming</span><span class="tag">SE · 20%</span></a>
            <a class="domain-row" href="k12.html"><span class="code">K12</span><span class="name">Het Weer</span><span class="tag">SE · 20%</span></a>
            <a class="domain-row" href="skills.html#po3"><span class="code">PO</span><span class="name">Practicum</span><span class="tag">SE · 20%</span></a>
        </div>

        <div class="section-label">Jaar 4 (GT4) — Periode 1 <small>· september–november</small></div>
        <div class="domain-list">
            <a class="domain-row" href="k5.html"><span class="code">K5</span><span class="name">Elektrische Energie</span><span class="tag">CE</span></a>
            <a class="domain-row" href="k9.html#deel1"><span class="code">K9</span><span class="name">Krachten &amp; Druk</span><span class="tag">CE · deel 1</span></a>
        </div>

        <div class="section-label">Jaar 4 (GT4) — Periode 2 <small>· november–februari</small></div>
        <div class="domain-list">
            <a class="domain-row" href="k6.html"><span class="code">K6</span><span class="name">Verbranden &amp; Verwarmen</span><span class="tag">CE</span></a>
            <a class="domain-row" href="k8.html"><span class="code">K8</span><span class="name">Geluid</span><span class="tag">CE</span></a>
            <a class="domain-row" href="k9.html#deel2"><span class="code">K9</span><span class="name">Beweging &amp; Veiligheid</span><span class="tag">CE · deel 2</span></a>
        </div>

        <div class="section-label">Jaar 4 (GT4) — Periode 3 <small>· februari–mei</small></div>
        <div class="domain-list">
            <a class="domain-row" href="k4.html"><span class="code">K4</span><span class="name">Stoffen &amp; Materialen</span><span class="tag">CE</span></a>
        </div>

        <a class="exam-banner" href="exam.html">
            <span><strong>Centraal Examen — donderdag 27 mei 2027</strong> · 50% van het eindcijfer</span>
            <span class="go">Examen-info →</span>
        </a>

        <p class="note-muted">
            Doorlopend: vaardigheden K1–K3 (onderzoeken, ontwerpen, informatie verwerken)
            lopen door beide jaren heen.
        </p>

        <footer>
            <span>VMBO-TL Natuurkunde Curriculum 2026-2027</span>
            <span>Gemaakt voor Agora</span>
        </footer>
    </div>
</body>
</html>
```

- [ ] **Step 2: Verify no stale references on index**

Run: `cd ~/Dropbox/ploxkevin.github.io/Routekaart && grep -c "polyfill\|MathJax\|2025-2026\|roadmap\|domain-card\|legend" index.html`
Expected: `0` (grep exits 1).

- [ ] **Step 3: Verify in browser**

Serve (server from Task 2 or restart) and check `http://localhost:8021/index.html`: gray field, white topbar/footer bars, five list blocks, one orange banner, no emoji, no legend.

- [ ] **Step 4: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io
git add Routekaart/index.html
git commit -m "Rewrite Routekaart index as DDOTT document with 2026-2027 content

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 4: Chrome-swap script for the 13 subpages

**Files:**
- Create (scratchpad, not committed): `<scratchpad>/transform_chrome.py`
- Modify (via script): `k4.html k5.html k6.html k7.html k8.html k9.html k10.html k11.html k12.html formulas.html skills.html exam.html learning_hierarchy.html`

**Interfaces:**
- Consumes: Task 2 classes (`.topbar`, `.eyebrow`, `.bottom-nav`, `.btn`, `.chip`).
- Produces: uniform chrome on all subpages; per-page `<header>` with eyebrow; year bumped; polyfill gone; MathJax only on the 8 math pages; emoji stripped. Content cards untouched.

- [ ] **Step 1: Write the transform script to `<scratchpad>/transform_chrome.py`:**

```python
#!/usr/bin/env python3
"""One-shot chrome swap for Routekaart subpages (idempotent via topbar marker)."""
import re, sys, pathlib

ROOT = pathlib.Path.home() / "Dropbox/ploxkevin.github.io/Routekaart"

MATH_PAGES = {"exam.html", "formulas.html", "k4.html", "k5.html",
              "k6.html", "k8.html", "k9.html", "k11.html"}

# file -> (eyebrow, h1)
HEADERS = {
    "k4.html":  ("Jaar 4 · Centraal examen · periode 3 (feb–mei)", "K4 — Stoffen en Materialen"),
    "k5.html":  ("Jaar 4 · Centraal examen · periode 1 (sep–nov)", "K5 — Elektrische Energie"),
    "k6.html":  ("Jaar 4 · Centraal examen · periode 2 (nov–feb)", "K6 — Verbranden en Verwarmen"),
    "k7.html":  ("Jaar 3 · Schoolexamen · weegt 20%", "K7 — Licht en Beeld"),
    "k8.html":  ("Jaar 4 · Centraal examen · periode 2 (nov–feb)", "K8 — Geluid"),
    "k9.html":  ("Jaar 4 · Centraal examen · periode 1 &amp; 2", "K9 — Kracht, Beweging en Veiligheid"),
    "k10.html": ("Jaar 3 · Schoolexamen · weegt 20%", "K10 — Bouw van de Materie"),
    "k11.html": ("Jaar 3 · Schoolexamen · weegt 20%", "K11 — Straling en Stralingsbescherming"),
    "k12.html": ("Jaar 3 · Schoolexamen · weegt 20%", "K12 — Het Weer"),
    "formulas.html": ("Centraal examen · 13 formules uit je hoofd", "Kernformules NaSk1"),
    "skills.html": ("Doorlopend · K1, K2 en K3", "Vaardighedenpiramide"),
    "exam.html": ("Jaar 4 · 50% van het eindcijfer", "Centraal Examen"),
    "learning_hierarchy.html": ("Overzicht · hoe kennis opbouwt", "Leerpiramide Natuurkunde"),
}

# curriculum order for the "Volgende:" button on domain pages
NEXT = {
    "k7.html":  ("k10.html", "K10 — Bouw van de Materie"),
    "k10.html": ("k11.html", "K11 — Straling"),
    "k11.html": ("k12.html", "K12 — Het Weer"),
    "k12.html": ("k5.html",  "K5 — Elektrische Energie (jaar 4)"),
    "k5.html":  ("k9.html#deel1", "K9 — Krachten &amp; Druk"),
    "k9.html":  ("k6.html", "K6 — Verbranden en Verwarmen"),
    "k6.html":  ("k8.html", "K8 — Geluid"),
    "k8.html":  ("k4.html", "K4 — Stoffen en Materialen"),
    "k4.html":  ("exam.html", "Centraal Examen"),
}

FONTS = ('    <link rel="preconnect" href="https://fonts.googleapis.com">\n'
         '    <link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>\n'
         '    <link href="https://fonts.googleapis.com/css2?family=Space+Grotesk:wght@400;500;700'
         '&family=Space+Mono:wght@400;700&display=swap" rel="stylesheet">\n')

TOPBAR = '''<div class="topbar">
            <a class="topbar-title" href="index.html">Natuurkunde Routekaart</a>
            <nav class="topbar-nav">
                <a href="index.html" class="chip">← Routekaart</a>
                <a href="formulas.html">Formules</a>
                <a href="skills.html">Vaardigheden</a>
                <a href="exam.html">Examen</a>
            </nav>
        </div>'''

FOOTER = '''<footer>
            <span>VMBO-TL Natuurkunde Curriculum 2026-2027</span>
            <span>Gemaakt voor Agora</span>
        </footer>'''

EMOJI = re.compile(
    "[\U0001F000-\U0001FAFF☀-➿⬀-⯿️⃣←↓]"
)
# NOTE: ← (left arrow) is stripped from content but our own chrome adds it
# back verbatim in TOPBAR/bottom-nav AFTER stripping, so order matters below.

def transform(name: str) -> None:
    path = ROOT / name
    html = path.read_text(encoding="utf-8")
    if 'class="topbar"' in html:
        print(f"SKIP {name} (already transformed)")
        return

    # 1) head: drop polyfill always; drop MathJax on non-math pages; add fonts
    html = re.sub(r'[ \t]*<script src="https://polyfill\.io[^\n]*\n', "", html)
    if name not in MATH_PAGES:
        html = re.sub(r'[ \t]*<script id="MathJax-script"[^\n]*\n', "", html)
    html = html.replace('    <link rel="stylesheet" href="style.css">',
                        FONTS + '    <link rel="stylesheet" href="style.css">')

    # 2) emoji strip (before injecting our own arrows), then tidy the space
    #    an emoji leaves behind at the start of headings
    html = EMOJI.sub("", html)
    html = re.sub(r"(<h[123][^>]*>)\s+", r"\1", html)

    # 3) nav -> topbar
    html = re.sub(r"<nav>.*?</nav>", TOPBAR, html, count=1, flags=re.S)

    # 4) header -> eyebrow + h1
    eyebrow, h1 = HEADERS[name]
    new_header = (f'<header>\n            <div class="eyebrow">{eyebrow}</div>\n'
                  f'            <h1>{h1}</h1>\n        </header>')
    html = re.sub(r"<header>.*?</header>", new_header, html, count=1, flags=re.S)

    # 5) back-link -> bottom-nav (domain pages get a next-button)
    if name in NEXT:
        href, label = NEXT[name]
        bottom = (f'<div class="bottom-nav">\n'
                  f'            <a class="btn" href="{href}">Volgende: {label}</a>\n'
                  f'            <a class="chip" href="index.html">← Terug naar de routekaart</a>\n'
                  f'        </div>')
        html = re.sub(r'<a href="index\.html" class="back-link">[^<]*</a>', bottom, html, count=1)
    else:
        html = re.sub(r'<a href="index\.html" class="back-link">[^<]*</a>',
                      '<a href="index.html" class="back-link">← Terug naar de routekaart</a>',
                      html, count=1)

    # 6) footer swap + year bump
    html = re.sub(r"<footer[^>]*>.*?</footer>", FOOTER, html, count=1, flags=re.S)
    html = html.replace("2025-2026", "2026-2027")

    path.write_text(html, encoding="utf-8")
    print(f"OK   {name}")

if __name__ == "__main__":
    for name in sys.argv[1:] or sorted(HEADERS):
        transform(name)
```

- [ ] **Step 2: Dry-run on one page and inspect**

```bash
cd ~/Dropbox/ploxkevin.github.io && python <scratchpad>/transform_chrome.py k7.html && git diff --stat Routekaart/k7.html && git diff Routekaart/k7.html | head -60
```
Expected: `OK k7.html`; diff shows polyfill+MathJax lines removed, fonts added, topbar/header/footer swapped, no content-card changes. If the diff looks wrong: `git checkout Routekaart/k7.html`, fix script, repeat.

- [ ] **Step 3: Run on all 13 subpages**

Run: `python <scratchpad>/transform_chrome.py`
Expected: `SKIP k7.html` + 12 × `OK`.

- [ ] **Step 4: Assert invariants across all pages**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
echo "polyfill (expect nothing):"; grep -l polyfill *.html
echo "MathJax pages (expect exactly 8):"; grep -l MathJax-script *.html | tr '\n' ' '; echo
echo "old year (expect nothing):"; grep -l "2025-2026" *.html
echo "topbar count (expect 14):"; grep -lc 'class="topbar"' *.html | wc -l
echo "anchors intact:"; grep -o 'id="deel[12]"' k9.html; grep -c 'id="\(k[123]\|po3\)"' skills.html
```
Expected: no polyfill hits; MathJax exactly `exam formulas k4 k5 k6 k8 k9 k11`; no 2025-2026; 14 topbars; `id="deel1" id="deel2"` and `4`.

- [ ] **Step 5: Visual spot-check** — `http://localhost:8021/k7.html`, `k9.html`, `formulas.html`: topbar, eyebrow+h1, white cards, orange next-button; MathJax renders on formulas.

- [ ] **Step 6: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io
git add Routekaart/*.html
git commit -m "Swap subpage chrome to DDOTT system, bump year, drop polyfill.io

MathJax retained only on the 8 pages containing TeX; emoji stripped;
anchors (deel1/deel2, k1-k3, po3) preserved.

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 5: exam.html facts (verified 2027 data)

**Files:**
- Modify: `Routekaart/exam.html` (post-Task-4 state)

**Interfaces:**
- Consumes: Task 4 chrome (eyebrow/h1 already set to "Centraal Examen").
- Produces: verified CE facts other pages link to; nothing downstream depends on exact wording.

- [ ] **Step 1: Replace the vague date bullet in the "Examendetails" info-box**

Old (inside `info-box info-danger`):
```html
<li><strong>Datum:</strong> Mei (exacte datum via Examenblad.nl)</li>
```
New:
```html
<li><strong>Datum:</strong> donderdag 27 mei 2027, 13:30–15:30 (tijdvak 1)</li>
<li><strong>Bron:</strong> <a href="https://www.examenblad.nl/2027/examenrooster">examenblad.nl/2027/examenrooster</a></li>
```

- [ ] **Step 2: Update the old header remnant** — the pre-Task-4 `<header>` said "Centraal Examen - Mei"; Task 4 set the h1 to "Centraal Examen". Extend the eyebrow with the date. In `exam.html` change:
```html
<div class="eyebrow">Jaar 4 · 50% van het eindcijfer</div>
```
to:
```html
<div class="eyebrow">Jaar 4 · 50% van het eindcijfer · donderdag 27 mei 2027</div>
```

- [ ] **Step 3: Verify**

Run: `grep -c "27 mei 2027" ~/Dropbox/ploxkevin.github.io/Routekaart/exam.html && grep -c "exacte datum" ~/Dropbox/ploxkevin.github.io/Routekaart/exam.html`
Expected: `2` (eyebrow + datum bullet) followed by `0` (grep exits 1 — the vague wording is gone).

- [ ] **Step 4: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io
git add Routekaart/exam.html
git commit -m "Fill in verified 2027 CE date for nask1 GL/TL (examenblad.nl)

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 6: learning_hierarchy.html pyramid restructure

**Files:**
- Modify: `Routekaart/learning_hierarchy.html` (post-Task-4 state)

**Interfaces:**
- Consumes: Task 2 `.hierarchy-level` styling (white rows, ink/orange left borders).
- Produces: nothing downstream.

- [ ] **Step 1: Remove the six arrow separator divs**

Delete every occurrence of:
```html
<div style="text-align: center; margin: 10px 0; font-size: 2em; color: #999;"></div>
```
(the ↓ glyph inside was already emoji-stripped by Task 4; the empty styled divs remain).

- [ ] **Step 2: Remove inline white link colors** — in the `level-5`, `level-2`, `level-1` rows change:
```html
<h3><a href="exam.html" style="color: white; text-decoration: none;">CENTRAAL EXAMEN</a></h3>
```
to
```html
<h3><a href="exam.html">Centraal Examen</a></h3>
```
and equivalently for the `k10.html` ("Kernconcept: deeltjesmodel (K10)") and `skills.html` ("Fundament: vaardigheden (K1, K2, K3)") links — drop the `style` attribute, keep href and text (de-shout the ALL-CAPS to sentence case as shown).

- [ ] **Step 3: Verify**

Run: `grep -c 'style="' ~/Dropbox/ploxkevin.github.io/Routekaart/learning_hierarchy.html`
Expected: `0`. Visual: six stacked white rows, top row orange-edged, bottom row muted.

- [ ] **Step 4: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io
git add Routekaart/learning_hierarchy.html
git commit -m "Restyle leerpiramide as typographic level list

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 7: Sitewide verification sweep

**Files:**
- Create (scratchpad, not committed): `<scratchpad>/check_links.py`

**Interfaces:**
- Consumes: all previous tasks.
- Produces: the go/no-go evidence for the user review gate.

- [ ] **Step 1: Write the link checker to `<scratchpad>/check_links.py`:**

```python
#!/usr/bin/env python3
"""Verify every local href/src target (file and #anchor) exists."""
import re, sys, pathlib

ROOT = pathlib.Path.home() / "Dropbox/ploxkevin.github.io/Routekaart"
pages = sorted(ROOT.glob("*.html"))
ids = {p.name: set(re.findall(r'id="([^"]+)"', p.read_text(encoding="utf-8"))) for p in pages}
broken, checked = [], 0

for p in pages:
    for href in re.findall(r'(?:href|src)="([^"]+)"', p.read_text(encoding="utf-8")):
        if href.startswith(("http", "mailto:", "data:")):
            continue
        checked += 1
        target, _, frag = href.partition("#")
        target = target or p.name
        if not (ROOT / target).exists():
            broken.append(f"{p.name}: missing file {href}")
        elif frag and target.endswith(".html") and frag not in ids.get(target, set()):
            broken.append(f"{p.name}: missing anchor {href}")

print(f"checked {checked} local refs across {len(pages)} pages")
print("\n".join(broken) if broken else "OK: 0 broken")
sys.exit(1 if broken else 0)
```

- [ ] **Step 2: Run the full assertion battery**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
python <scratchpad>/check_links.py
echo "---"; grep -rln "polyfill\|2025-2026" *.html *.css; echo "(expect nothing)"
echo "---"; python3 -c "
import pathlib,re
for p in sorted(pathlib.Path('.').glob('*.html')):
    t=p.read_text(encoding='utf-8')
    e=[c for c in t if ord(c)>=0x1F000 or 0x2600<=ord(c)<=0x27BF]
    if e: print(p.name, e)
print('emoji scan done')"
```
Expected: `OK: 0 broken`; no polyfill/year hits; `emoji scan done` with no page lines.

- [ ] **Step 3: Serve for user review and STOP**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart && python -m http.server 8021
```
Tell the user: review `http://localhost:8021/` (index + a few domain pages + formulas math rendering + print preview). **Do not proceed to Task 8 without explicit approval.**

---

### Task 8: Mirror to Agora copy and hand off deployment

**Files:**
- Modify: `~/Dropbox/Agora/Routekaart/*.html`, `style.css` (mirror of deployed dir)

**Interfaces:**
- Consumes: user approval from Task 7.
- Produces: consistent working copy; deployment stays user-gated.

- [ ] **Step 1: Mirror site files (only after user approval)**

```bash
rsync -av --include="*.html" --include="style.css" --exclude="*" \
  ~/Dropbox/ploxkevin.github.io/Routekaart/ ~/Dropbox/Agora/Routekaart/
```
Expected: 15 html + 1 css transferred; Agora extras (sections/, README, PTA pdf, .nojekyll) untouched.

- [ ] **Step 2: Delete stale artifacts in the Agora copy too**

```bash
rm -f ~/Dropbox/Agora/Routekaart/main.aux ~/Dropbox/Agora/Routekaart/main.log ~/Dropbox/Agora/Routekaart/main.out
```

- [ ] **Step 3: Stop the brainstorm companion server**

```bash
/home/oxrexkevin/.claude/plugins/cache/claude-plugins-official/superpowers/6.1.1/skills/brainstorming/scripts/stop-server.sh \
  ~/Dropbox/ploxkevin.github.io/.superpowers/brainstorm/96716-1783560508
```

- [ ] **Step 4: Offer deployment** — ask the user whether to `git push` (deploys to GitHub Pages). Never push unprompted.

---

## Plan Self-Review (completed 2026-07-09)

- **Spec coverage:** tokens/type/links/buttons → Task 2; index restructure + legend removal + CE banner → Task 3; subpage chrome, emoji strip, year bump, polyfill removal, MathJax scoping, anchors → Task 4; verified exam facts → Task 5; pyramid → Task 6; verification battery + review gate → Task 7; Agora mirror + push gate → Task 8; artifacts + gitignore → Task 1.
- **Placeholders:** none — every step carries exact code/commands (`<scratchpad>` expands to the session scratchpad path in Global Constraints).
- **Type consistency:** class names in Task 2 CSS match Task 3 HTML and Task 4 script output (`topbar`, `topbar-nav`, `chip`, `eyebrow`, `domain-list/row/code/name/tag`, `exam-banner`, `bottom-nav`, `btn`, `back-link`, `section-label`, `note-muted`, `hierarchy-level`).
- **Known intentional deviations:** exact CE date shown on index banner (spec said "mei 2027"; verified date is stronger and spec-compliant in intent). Post-review additions (2026-07-09, final whole-branch review): type scale adapted down from the DDOTT foundry source (h2 24px, h3 18px, eyebrow 13px vs the spec's original 32/28/16px prose — spec updated to match shipped values); button box height 37px (35px line-height + 2×1px border); leerpiramide gradation expressed via left-border color rather than size/indentation (spec updated).
