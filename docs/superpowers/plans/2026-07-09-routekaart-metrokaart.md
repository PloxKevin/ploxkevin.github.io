# NSK1 Metrokaart + Cohort-Split Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add the official-format metrokaart page for cohort 2026–2028 and split the index into two cohort lanes, with NSK1-code corrections across domain pages and a cohort-aware exam page.

**Architecture:** One new static page (`routekaart.html`) with a hand-authored inline SVG metro line in the existing DDOTT token system; `index.html` body is rewritten (two cohort lanes); seven files get exact-string edits. No JS, no build step. All station facts flow from the spec's canonical station table.

**Tech Stack:** Plain HTML/CSS + inline SVG, existing `style.css` token system, Python 3 (verification scripts in scratchpad only).

## Global Constraints

- Working dir: `~/Dropbox/ploxkevin.github.io/Routekaart/` on branch **`metrokaart-2026-2028`** (create from `main` in Task 1). **NEVER `git push`** — push = deploy, user-gated.
- Spec: `docs/superpowers/specs/2026-07-09-routekaart-metrokaart-design.md`. Its canonical station table is the single source of truth; if any value below disagrees with the spec, the spec wins.
- Flexibiliteit (user-approved): NSK1-2 and NSK1-3 = flexibel (ster + dashed circle); NSK1-1, NSK1-4, NSK1-5 = inflexibel; **no dubbel-inzetbaar pills on stations** (legend shows them marked "nog niet in gebruik").
- Ster-footnote, verbatim wherever a ster appears (index lane 2 + routekaart.html): `*PTA-onderdelen met * kunnen in willekeurige volgorde worden afgerond. De inlevermaand wordt dan gewisseld met een ander PTA-onderdeel.`
- Honesty: period labels only, never months; every station label carries `data-maand=""`; CE 2028 is "voorjaar 2028"; metro page footer note `Gebaseerd op PTA NSK1 vmbo-TL 2028 (overgangsversie)`.
- Tokens/colors: line + symbols `#ff6b17` (`--accent`), never white text on orange; `border-radius: 0`; no gradients.
- All UI copy Dutch. Preserve every existing anchor id.
- Helper scripts live in `/tmp/claude-1000/-home-oxrexkevin/d766e6e1-1b21-4842-aa02-5853a01a85c1/scratchpad`, NOT committed.
- Commit after every task; end commit messages with:
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>` and
  `Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV`

---

### Task 1: Branch + CSS metro block

**Files:**
- Modify: `Routekaart/style.css` (append one block at end, after the `@media print` block — and add one line INSIDE the print block)

**Interfaces:**
- Consumes: existing tokens (`--accent`, `--ink`, `--muted`, `--line`, `--surface`, `--shadow-pop`, `--font-ui`).
- Produces: classes used by Tasks 2–3: `.metro-scroll`, `.metro-svg`, `.metro-station-name`, `.metro-station-meta`, `.metro-caption`, `.metro-legend-title`, `.metro-line-name`, `.metro-note`.

- [ ] **Step 1: Create the branch**

```bash
cd ~/Dropbox/ploxkevin.github.io && git checkout main && git checkout -b metrokaart-2026-2028
```
Expected: `Switched to a new branch 'metrokaart-2026-2028'`.

- [ ] **Step 2: Append the metro CSS block to `Routekaart/style.css`** (after the final closing brace of the `@media print` block):

```css

/* ---- Metrokaart (routekaart.html) ---- */
.metro-scroll {
    background: var(--surface);
    border: 1px solid var(--line);
    box-shadow: var(--shadow-pop);
    overflow-x: auto;
    margin: 14px 0;
}
.metro-scroll svg { display: block; min-width: 900px; width: 100%; height: auto; }
.metro-svg text { font-family: var(--font-ui); }
.metro-station-name { fill: var(--ink); font-size: 13px; font-weight: 500; }
.metro-station-meta { fill: var(--muted); font-size: 12px; }
.metro-caption { fill: var(--muted); font-size: 12px; }
.metro-legend-title { fill: var(--ink); font-size: 12.5px; font-weight: 700; }
.metro-line-name { fill: var(--ink); font-size: 13px; font-weight: 500; }
.metro-note { font-size: 13px; color: var(--muted); margin: 6px 0 14px; }
```

- [ ] **Step 3: Add the print rule** — inside the existing `@media print { … }` block, after the `.exam-banner` rule, add:

```css
    .metro-scroll { overflow: visible; border: none; box-shadow: none; }
```

- [ ] **Step 4: Verify**

Run: `cd ~/Dropbox/ploxkevin.github.io/Routekaart && grep -c "metro-" style.css && grep -A3 "@media print" style.css | head -8`
Expected: `10` metro- occurrences (9 in the block + 1 in print) — count them; and the print block shows the new rule. Also `grep -c "gradient" style.css` → `0`.

- [ ] **Step 5: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io && git add Routekaart/style.css && git commit -m "Add metrokaart CSS block to token system

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 2: Create `Routekaart/routekaart.html`

**Files:**
- Create: `Routekaart/routekaart.html` (complete content below)

**Interfaces:**
- Consumes: Task 1 CSS classes; site chrome pattern (topbar/footer identical to other subpages).
- Produces: link target `routekaart.html` used by Tasks 3–4.

- [ ] **Step 1: Create the file with exactly this content:**

```html
<!DOCTYPE html>
<html lang="nl">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Metrokaart NSK1 cohort 2026-2028 - Natuurkunde Routekaart</title>
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
                <a href="index.html" class="chip">← Routekaart</a>
                <a href="formulas.html">Formules</a>
                <a href="skills.html">Vaardigheden</a>
                <a href="exam.html">Examen</a>
            </nav>
        </div>

        <header>
            <div class="eyebrow">Cohort 2026–2028 · VMBO-TL · PTA 2028</div>
            <h1>Metrokaart natuurkunde (NSK1)</h1>
        </header>

        <p>
            Deze metrokaart toont de route van het cohort dat in 2026 in leerjaar 3 start:
            vijf PTA-stations in leerjaar 3, daarna een leerjaar 4 dat volledig in het teken
            staat van examenvoorbereiding, met het centraal examen in het voorjaar van 2028
            als eindstation. Stations met een ster (gestippelde cirkel) mag je in overleg in
            een andere volgorde afronden. Datapunten — de kleine bolletjes met taken en
            activiteiten — worden in de loop van het jaar toegevoegd.
        </p>

        <!-- ==================================================================
             DATAPUNTEN TOEVOEGEN (voor de docent):
             Kopieer per datapunt het voorbeeldblok hieronder in de SVG, direct
             na de regel <g id="datapunten">. Kies cx tussen twee stations op de
             lijn (y=310 op het leerjaar-3-deel). Voorbeeld:

             <g class="metro-datapunt">
                 <circle cx="195" cy="310" r="5" fill="#ff6b17"/>
                 <text class="metro-station-meta" data-maand=""
                       transform="rotate(-45 195 286)" x="195" y="286"
                       text-anchor="start">Feedbackmoment practicumverslag</text>
             </g>
             ================================================================== -->

        <div class="metro-scroll">
        <svg class="metro-svg" viewBox="0 0 1200 430" role="img" aria-labelledby="metro-title" xmlns="http://www.w3.org/2000/svg">
            <title id="metro-title">Metrokaart NSK1 cohort 2026-2028; de tabel onder de kaart bevat dezelfde informatie</title>

            <!-- jaargrens -->
            <line x1="880" y1="150" x2="880" y2="360" stroke="#dddddd" stroke-width="1"/>
            <text class="metro-caption" x="880" y="140" text-anchor="middle">zomer 2027</text>

            <!-- metrolijn -->
            <path d="M 40 310 H 820 L 940 190 H 1140" fill="none" stroke="#ff6b17" stroke-width="6" stroke-linecap="round" stroke-linejoin="round"/>

            <!-- leerjaar-labels -->
            <text class="metro-caption" x="430" y="352" text-anchor="middle">Leerjaar 3 · 2026–2027 · alle SE-toetsen</text>
            <text class="metro-caption" x="1040" y="160" text-anchor="middle">
                <tspan x="1040" dy="0">Leerjaar 4 · 2027–2028</tspan>
                <tspan x="1040" dy="15">CE-voorbereiding (K4–K9, V1, V2)</tspan>
            </text>

            <g id="datapunten"></g>

            <!-- station NSK1-1 (inflexibel) -->
            <a href="skills.html#po3">
                <circle cx="120" cy="310" r="13" fill="#ffffff" stroke="#ff6b17" stroke-width="4"/>
                <text transform="rotate(-45 120 340)" x="120" y="340" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">NSK1-1 · Praktische opdracht</tspan>
                    <tspan class="metro-station-meta" x="120" dy="16">periode 1 · PO · 20% · niet herkansbaar</tspan>
                </text>
            </a>

            <!-- station NSK1-2 (flexibel*) -->
            <a href="k7.html">
                <circle cx="270" cy="310" r="13" fill="#ffffff" stroke="#ff6b17" stroke-width="4" stroke-dasharray="7 5"/>
                <text transform="rotate(-45 270 340)" x="270" y="340" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">*NSK1-2 · Licht en beeld</tspan>
                    <tspan class="metro-station-meta" x="270" dy="16">periode 2 · S · 20%</tspan>
                </text>
            </a>

            <!-- station NSK1-3 (flexibel*) -->
            <a href="k10.html">
                <circle cx="420" cy="310" r="13" fill="#ffffff" stroke="#ff6b17" stroke-width="4" stroke-dasharray="7 5"/>
                <text transform="rotate(-45 420 340)" x="420" y="340" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">*NSK1-3 · Bouw van de materie</tspan>
                    <tspan class="metro-station-meta" x="420" dy="16">periode 2 · S/M · 20%</tspan>
                </text>
            </a>

            <!-- station NSK1-4 (inflexibel) -->
            <a href="k11.html">
                <circle cx="570" cy="310" r="13" fill="#ffffff" stroke="#ff6b17" stroke-width="4"/>
                <text transform="rotate(-45 570 340)" x="570" y="340" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">NSK1-4 · Straling</tspan>
                    <tspan class="metro-station-meta" x="570" dy="16">periode 3 · S · 20%</tspan>
                </text>
            </a>

            <!-- station NSK1-5 (inflexibel) -->
            <a href="k12.html">
                <circle cx="720" cy="310" r="13" fill="#ffffff" stroke="#ff6b17" stroke-width="4"/>
                <text transform="rotate(-45 720 340)" x="720" y="340" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">NSK1-5 · Het weer</tspan>
                    <tspan class="metro-station-meta" x="720" dy="16">periode 4 · S · 20%</tspan>
                </text>
            </a>

            <!-- terminus: Centraal Examen -->
            <a href="exam.html">
                <circle cx="1140" cy="190" r="16" fill="#ffffff" stroke="#ff6b17" stroke-width="5"/>
                <circle cx="1140" cy="190" r="5" fill="#ff6b17"/>
                <text transform="rotate(-45 1140 226)" x="1140" y="226" text-anchor="end">
                    <tspan class="metro-station-name" data-maand="">Centraal Examen</tspan>
                    <tspan class="metro-station-meta" x="1140" dy="16">voorjaar 2028 · 50% eindcijfer</tspan>
                </text>
            </a>

            <!-- lijnnaam linksonder -->
            <rect x="40" y="408" width="28" height="6" fill="#ff6b17"/>
            <text class="metro-line-name" x="76" y="415">NSK1 — natuurkunde</text>

            <!-- legenda rechtsonder -->
            <g>
                <text class="metro-legend-title" x="950" y="300">Legenda</text>
                <circle cx="958" cy="318" r="7" fill="#ffffff" stroke="#ff6b17" stroke-width="3"/>
                <text class="metro-caption" x="974" y="322">inflexibel PTA</text>
                <circle cx="958" cy="340" r="7" fill="#ffffff" stroke="#ff6b17" stroke-width="3" stroke-dasharray="4 3"/>
                <text class="metro-caption" x="974" y="344">flexibel PTA *</text>
                <circle cx="958" cy="362" r="4" fill="#ff6b17"/>
                <text class="metro-caption" x="974" y="366">datapunt (volgt)</text>
                <circle cx="954" cy="384" r="7" fill="#ffffff" stroke="#ff6b17" stroke-width="3"/>
                <ellipse cx="967" cy="384" rx="3.5" ry="8" fill="#ffffff" stroke="#ff6b17" stroke-width="2.5"/>
                <text class="metro-caption" x="980" y="388">dubbel inzetbaar (nog niet in gebruik)</text>
                <circle cx="954" cy="406" r="7" fill="#ffffff" stroke="#ff6b17" stroke-width="3" stroke-dasharray="4 3"/>
                <ellipse cx="967" cy="406" rx="3.5" ry="8" fill="#ffffff" stroke="#ff6b17" stroke-width="2.5"/>
                <text class="metro-caption" x="980" y="410">dubbel inzetbaar flexibel (nog niet in gebruik)</text>
            </g>
        </svg>
        </div>

        <p class="metro-note">*PTA-onderdelen met * kunnen in willekeurige volgorde worden afgerond. De inlevermaand wordt dan gewisseld met een ander PTA-onderdeel.</p>

        <h2>Alle stations in tabelvorm</h2>
        <table>
            <tr><th>Code</th><th>Inhoud</th><th>Periode</th><th>Vorm</th><th>Herkansbaar</th><th>Weging</th><th>Aansluiting nieuw programma (indicatief)</th></tr>
            <tr><td><strong>NSK1-1</strong></td><td><a href="skills.html#po3">Praktische opdracht — onderzoeks- en ontwerpvaardigheden</a></td><td>Lj3 · P1</td><td>P</td><td>nee</td><td>20%</td><td>Domein E (E1, E2) · C · F</td></tr>
            <tr><td><strong>*NSK1-2</strong></td><td><a href="k7.html">Licht en beeld</a></td><td>Lj3 · P2</td><td>S</td><td>ja</td><td>20%</td><td>B5 (eindterm 15, oog) · C</td></tr>
            <tr><td><strong>*NSK1-3</strong></td><td><a href="k10.html">Bouw van de materie</a></td><td>Lj3 · P2</td><td>S/M</td><td>ja</td><td>20%</td><td>B3 · A</td></tr>
            <tr><td><strong>NSK1-4</strong></td><td><a href="k11.html">Straling en stralingsbescherming</a></td><td>Lj3 · P3</td><td>S</td><td>ja</td><td>20%</td><td>B3 · C</td></tr>
            <tr><td><strong>NSK1-5</strong></td><td><a href="k12.html">Het weer</a></td><td>Lj3 · P4</td><td>S</td><td>ja</td><td>20%</td><td>B5 (eindterm 16, systeem aarde) · D2</td></tr>
            <tr><td>—</td><td><a href="exam.html">Centraal Examen (eindstation)</a></td><td>voorjaar 2028</td><td>CE</td><td>—</td><td>50% eindcijfer</td><td>huidig programma K1–K12</td></tr>
        </table>

        <p>
            Het schoolexamen wordt volledig afgesloten aan het einde van leerjaar 3. Het
            SE-cijfer is het gewogen gemiddelde van de vijf onderdelen, afgerond op één
            decimaal. Leerjaar 4 is volledig gericht op de voorbereiding van het centraal
            examen.
        </p>

        <p class="metro-note">Gebaseerd op PTA NSK1 vmbo-TL 2028 (overgangsversie).</p>

        <footer>
            <span>VMBO-TL Natuurkunde Curriculum 2026-2027</span>
            <span>Gemaakt voor Agora</span>
        </footer>
    </div>
</body>
</html>
```

- [ ] **Step 2: Verify structure**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
python3 -c "
import re
t = open('routekaart.html', encoding='utf-8').read()
assert t.count('stroke-dasharray=\"7 5\"') == 2, 'need exactly 2 flexibele stations'
assert t.count('<a href=') >= 10, 'station+table links'
assert 'PTA-onderdelen met * kunnen' in t, 'footnote'
assert 'data-maand=\"\"' in t and t.count('data-maand') == 7, '7 month slots (6 live + 1 in the teacher template comment)'
assert 'overgangsversie' in t, 'version note'
maanden = ['januari','februari','maart','april','mei','juni','juli','augustus','september','oktober','november','december']
assert not any(re.search(r'\b' + m + r'\b', t.lower()) for m in maanden), 'no month labels allowed (word-boundary check; Domein/inlevermaand are fine)'
assert 'voorjaar 2028' in t
print('OK: structure checks pass')"
```
Expected: `OK: structure checks pass`

- [ ] **Step 3: Visual check** — serve (`python -m http.server 8021`, then kill) or open the file; confirm: orange line with bend, 5 stations + terminus, dashed circles on NSK1-2/3 only, legend rechtsonder with 5 symbols, table below.

- [ ] **Step 4: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io && git add Routekaart/routekaart.html && git commit -m "Add NSK1 metrokaart page for cohort 2026-2028 (official Agora format)

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 3: index.html cohort lanes

**Files:**
- Modify: `Routekaart/index.html` (body restructure; head unchanged)

**Interfaces:**
- Consumes: `routekaart.html` (Task 2), existing classes + `.note-muted`, `.exam-banner`, `.section-label`, `.domain-list`, `.domain-row`.
- Produces: nothing downstream.

- [ ] **Step 1: Replace the two intro paragraphs** (currently starting `Deze routekaart beschrijft het volledige natuurkundecurriculum.` and `Sneller navigeren:`) with:

```html
        <p>
            Deze routekaart beschrijft het natuurkundecurriculum voor twee cohorten. Het
            huidige leerjaar 4 (cohort 2025–2027) bereidt voor op het
            <a href="exam.html">centraal examen van 27 mei 2027</a>. Het nieuwe leerjaar 3
            (cohort 2026–2028) sluit alle schoolexamens af in leerjaar 3 en doet
            <a href="exam.html">centraal examen in het voorjaar van 2028</a>. Het
            eindcijfer is voor beide cohorten 50% SE + 50% CE. Klik op een onderdeel voor
            leerdoelen, formules, practicum en typische examenvragen.
        </p>
        <p style="font-size: 13.5px;">
            Sneller navigeren: <a href="routekaart.html">Metrokaart 2026–2028</a> ·
            <a href="learning_hierarchy.html">Leerpiramide</a> ·
            <a href="skills.html">Vaardigheden K1–K3</a> ·
            <a href="formulas.html">13 kernformules</a> ·
            <a href="exam.html">Examen-info</a>
        </p>
```

- [ ] **Step 2: Insert Lane-1 label** — directly before the existing `<div class="section-label">Jaar 4 (GT4) — Periode 1 <small>· september–november</small></div>`, insert:

```html
        <div class="section-label" style="font-size: 14px;">GT4 · Cohort 2025–2027 <small>· leerjaar 4 · CE-voorbereiding · CE: 27 mei 2027</small></div>
```

And change the three existing jaar-4 section-labels from `Jaar 4 (GT4) — Periode N` to `Periode N` (keeping their `<small>` month spans), e.g. `<div class="section-label">Periode 1 <small>· september–november</small></div>`.

- [ ] **Step 3: Replace the Jaar-3 block with Lane 2** — delete the block from `<div class="section-label">Jaar 3 (GT3) — 100% schoolexamen <small>· augustus–juni</small></div>` through its closing `</div>` of the domain-list (the 5 rows K7/K10/K11/K12/PO), and insert AFTER the existing exam banner (`</a>` of `.exam-banner`) and BEFORE the doorlopend `note-muted` paragraph:

```html
        <div class="section-label" style="font-size: 14px;">GT3 · Cohort 2026–2028 <small>· leerjaar 3 · 100% schoolexamen (PTA 2028)</small></div>
        <div class="domain-list">
            <a class="domain-row" href="skills.html#po3"><span class="code">NSK1-1</span><span class="name">Praktische opdracht</span><span class="tag">P1 · PO · 20%</span></a>
            <a class="domain-row" href="k7.html"><span class="code">*NSK1-2</span><span class="name">Licht &amp; Beeld</span><span class="tag">P2 · S · 20%</span></a>
            <a class="domain-row" href="k10.html"><span class="code">*NSK1-3</span><span class="name">Bouw van de Materie</span><span class="tag">P2 · S/M · 20%</span></a>
            <a class="domain-row" href="k11.html"><span class="code">NSK1-4</span><span class="name">Straling en Stralingsbescherming</span><span class="tag">P3 · S · 20%</span></a>
            <a class="domain-row" href="k12.html"><span class="code">NSK1-5</span><span class="name">Het Weer</span><span class="tag">P4 · S · 20%</span></a>
        </div>

        <a class="exam-banner" href="routekaart.html">
            <span><strong>Metrokaart cohort 2026–2028</strong> · alle stations op één lijn</span>
            <span class="go">Bekijk de kaart →</span>
        </a>

        <p class="note-muted">*PTA-onderdelen met * kunnen in willekeurige volgorde worden afgerond. De inlevermaand wordt dan gewisseld met een ander PTA-onderdeel.</p>
```

The resulting body order: topbar → header → intro → quick-nav → **Lane 1 label → Periode 1/2/3 lists → CE-2027 banner** → **Lane 2 label → NSK1 list → metrokaart banner → ster-footnote** → doorlopend note → footer. The `.code` column of Lane 2 is wider than K-codes; no CSS change needed (`min-width` is a floor, rows flex).

- [ ] **Step 4: Verify**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
python3 -c "
t = open('index.html', encoding='utf-8').read()
assert t.count('exam-banner') == 2, 'two banners (CE + metrokaart)'
assert t.index('Cohort 2025–2027') < t.index('Cohort 2026–2028'), 'lane order'
assert t.count('NSK1-') == 5, '5 NSK1 rows'
assert 'Jaar 3 (GT3)' not in t, 'old jaar-3 block gone'
assert t.count('PTA-onderdelen met * kunnen') == 1, 'footnote once'
assert 'routekaart.html' in t
assert 'k9.html#deel1' in t and 'k9.html#deel2' in t and 'skills.html#po3' in t, 'anchors kept'
print('OK: index checks pass')"
```
Expected: `OK: index checks pass`

- [ ] **Step 5: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io && git add Routekaart/index.html && git commit -m "Split index into two cohort lanes (GT4 2025-2027, GT3 2026-2028)

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 4: NSK1 corrections on domain/skills/exam pages

**Files:**
- Modify: `Routekaart/k7.html`, `k10.html`, `k11.html`, `k12.html`, `skills.html`, `exam.html` (exact-string edits below; line numbers are current as of 2026-07-09, use the strings not the numbers)

**Interfaces:**
- Consumes: `routekaart.html` link target.
- Produces: nothing downstream.

- [ ] **Step 1: k7.html** — two edits:

Old: `<div class="eyebrow">Jaar 3 · Schoolexamen · weegt 20%</div>`
New: `<div class="eyebrow">Jaar 3 · Schoolexamen · NSK1-2 · periode 2 · weegt 20%</div>`

Old: `<td>20% (OND2)</td>`
New: `<td>20% (NSK1-2 · herkansbaar · cohort 2026–2028)</td>`

Old: `<td>GT3, typisch periode 2</td>`
New: `<td>GT3, periode 2 (cohort 2026–2028)</td>`

- [ ] **Step 2: k10.html** — three edits:

Old: `<div class="eyebrow">Jaar 3 · Schoolexamen · weegt 20%</div>`
New: `<div class="eyebrow">Jaar 3 · Schoolexamen · NSK1-3 · periode 2 · weegt 20%</div>`

Old: `<td>GT3, typisch periode 2-3</td>`
New: `<td>GT3, periode 2 (cohort 2026–2028)</td>`

Old: `<td>20% (OND3)</td>`
New: `<td>20% (NSK1-3 · herkansbaar · cohort 2026–2028)</td>`

- [ ] **Step 3: k11.html** — three edits:

Old: `<div class="eyebrow">Jaar 3 · Schoolexamen · weegt 20%</div>`
New: `<div class="eyebrow">Jaar 3 · Schoolexamen · NSK1-4 · periode 3 · weegt 20%</div>`

Old: `<td>GT3, typisch periode 3</td>`
New: `<td>GT3, periode 3 (cohort 2026–2028)</td>`

Old: `<td>20% (OND4)</td>`
New: `<td>20% (NSK1-4 · herkansbaar · cohort 2026–2028)</td>`

- [ ] **Step 4: k12.html** — three edits:

Old: `<div class="eyebrow">Jaar 3 · Schoolexamen · weegt 20%</div>`
New: `<div class="eyebrow">Jaar 3 · Schoolexamen · NSK1-5 · periode 4 · weegt 20%</div>`

Old: `<td>GT3, typisch periode 1</td>`
New: `<td>GT3, periode 4 (cohort 2026–2028)</td>`

Old: `<td>20% (OND5)</td>`
New: `<td>20% (NSK1-5 · herkansbaar · cohort 2026–2028)</td>`

- [ ] **Step 5: skills.html** — three edits:

After the line `<h2>Practicum (PO) - 20% Weging</h2>` insert:
```html
            <p><strong>NSK1-1</strong> · periode 1 · praktische opdracht met verslag · niet herkansbaar · weegt 20% <small>(cohort 2026–2028, PTA 2028)</small></p>
```

Old: `20% weging in OND1` → New: `20% weging in NSK1-1`
Old: `geïntegreerd in practicum (OND1)` → New: `geïntegreerd in practicum (NSK1-1)`

- [ ] **Step 6: exam.html** — two edits:

Old: `<div class="eyebrow">Jaar 4 · 50% van het eindcijfer · donderdag 27 mei 2027</div>`
New: `<div class="eyebrow">Jaar 4 · 50% van het eindcijfer · per cohort hieronder</div>`

Old (the whole Examendetails info-box):
```html
            <div class="info-box info-danger">
                <h3>Examendetails</h3>
                <ul>
                    <li><strong>Weging:</strong> 50% van eindcijfer</li>
                    <li><strong>Duur:</strong> 2 uur (120 minuten)</li>
                    <li><strong>Datum:</strong> donderdag 27 mei 2027, 13:30–15:30 (tijdvak 1)</li>
                    <li><strong>Bron:</strong> <a href="https://www.examenblad.nl/2027/examenrooster">examenblad.nl/2027/examenrooster</a></li>
                </ul>
            </div>
```
New:
```html
            <div class="info-box info-danger">
                <h3>Examendetails — cohort 2025–2027 (huidig leerjaar 4)</h3>
                <ul>
                    <li><strong>Weging:</strong> 50% van eindcijfer</li>
                    <li><strong>Duur:</strong> 2 uur (120 minuten)</li>
                    <li><strong>Datum:</strong> donderdag 27 mei 2027, 13:30–15:30 (tijdvak 1)</li>
                    <li><strong>Bron:</strong> <a href="https://www.examenblad.nl/2027/examenrooster">examenblad.nl/2027/examenrooster</a></li>
                </ul>
            </div>

            <div class="info-box info-primary">
                <h3>Cohort 2026–2028 (start leerjaar 3 in 2026)</h3>
                <ul>
                    <li><strong>Centraal examen:</strong> voorjaar 2028 (exacte datum volgt via examenblad.nl)</li>
                    <li><strong>Schoolexamen:</strong> volledig afgesloten in leerjaar 3 (2026-2027), vijf onderdelen à 20%</li>
                    <li><strong>Route:</strong> <a href="routekaart.html">bekijk de metrokaart van dit cohort</a></li>
                </ul>
            </div>
```

- [ ] **Step 7: Verify**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
grep -c "OND[0-9]" *.html; echo "expect no output above (grep exits 1)"
grep -l "cohort 2026–2028" k7.html k10.html k11.html k12.html skills.html exam.html | wc -l
grep -c "routekaart.html" exam.html
```
Expected: OND grep silent (exit 1); `6`; `1`.

- [ ] **Step 8: Commit**

```bash
cd ~/Dropbox/ploxkevin.github.io && git add Routekaart/k7.html Routekaart/k10.html Routekaart/k11.html Routekaart/k12.html Routekaart/skills.html Routekaart/exam.html && git commit -m "Correct pages to NSK1 codes and PTA-2028 periods, cohort-aware exam page

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_011L3pQo2a9mRNoGzfvY15yV"
```

---

### Task 5: Battery + codex format-compliance review

**Files:**
- Reuse: `<scratchpad>/check_links.py` (exists from the redesign; recreate from the redesign plan Task 7 if missing)

**Interfaces:**
- Consumes: all previous tasks.
- Produces: evidence for the user review gate.

- [ ] **Step 1: Run the extended battery**

```bash
cd ~/Dropbox/ploxkevin.github.io/Routekaart
python3 /tmp/claude-1000/-home-oxrexkevin/d766e6e1-1b21-4842-aa02-5853a01a85c1/scratchpad/check_links.py
grep -rln "polyfill\|2025-2026\|OND[0-9]" *.html *.css; echo "stale exit: $?"
python3 -c "
import pathlib
foot = 'PTA-onderdelen met * kunnen in willekeurige volgorde worden afgerond'
for f in ['index.html', 'routekaart.html']:
    t = pathlib.Path(f).read_text(encoding='utf-8')
    assert foot in t, f + ' missing footnote'
assert 'maand' not in pathlib.Path('routekaart.html').read_text(encoding='utf-8').replace('data-maand','').replace('inlevermaand',''), 'no month labels'
print('OK: footnote + honesty checks pass')"
```
Expected: `checked ≥150 local refs across 15 pages` + `OK: 0 broken`; stale grep silent (exit 1); `OK: footnote + honesty checks pass`.

- [ ] **Step 2: Codex format-compliance review** (user's standing instruction)

```bash
/usr/bin/codex exec --skip-git-repo-check "Review /home/oxrexkevin/Dropbox/ploxkevin.github.io/Routekaart/routekaart.html and /home/oxrexkevin/Dropbox/ploxkevin.github.io/Routekaart/index.html (read-only) against the official Agora metrokaart format described in /tmp/claude-1000/-home-oxrexkevin/d766e6e1-1b21-4842-aa02-5853a01a85c1/scratchpad/routekaart-format/format-context.md and the PTA facts in /tmp/claude-1000/-home-oxrexkevin/d766e6e1-1b21-4842-aa02-5853a01a85c1/scratchpad/routekaart-format/pta-2028-digest.md. Check: (1) symbol grammar (open=inflexibel on NSK1-1/4/5, dashed=flexibel on NSK1-2/3 only, no pills on stations, legend complete incl. unused pill variants); (2) PTA labels below line with code+naam+periode, datapunten area above line, footnote verbatim; (3) every PTA fact (periode, vorm, herkansbaar, weging) matches the xlsx digest; (4) no invented months/dates anywhere (only 'voorjaar 2028' for CE); (5) both cohort lanes on index factually correct. Report PASS/FAIL per point with evidence." 2>&1 | tail -30
```
Expected: PASS on all five points. Any FAIL → fix, re-run battery + codex, then continue.

- [ ] **Step 3: No commit** (read-only task). Record outputs in the task report.

---

### Task 6: User review gate + merge/deploy handoff (controller-level)

- [ ] **Step 1:** Serve `Routekaart/` on port 8021, present `http://localhost:8021/routekaart.html` and `index.html` to the user. **STOP for explicit approval.**
- [ ] **Step 2 (after approval):** finishing-a-development-branch flow — battery as "tests", merge `metrokaart-2026-2028` to `main`, delete branch.
- [ ] **Step 3:** Mirror to the Agora working copy:
```bash
rsync -av --include="*.html" --include="style.css" --exclude="*" ~/Dropbox/ploxkevin.github.io/Routekaart/ ~/Dropbox/Agora/Routekaart/
```
- [ ] **Step 4:** Offer `git push` (= deploy). Never push unprompted. After deploy: verify live with `curl -s https://ploxkevin.github.io/Routekaart/routekaart.html | grep -c "Metrokaart"` ≥ 1 (allow CDN propagation time).

---

## Plan Self-Review (completed 2026-07-09)

- **Spec coverage:** canonical table → Task 2 SVG/table + Task 3 lane 2 (values identical); metro page anatomy incl. legend/lijnnaam/datapunt template/aria → Task 2; CSS → Task 1; two-lane index → Task 3; domain/skills/exam corrections → Task 4 (k11 period was already correct — only eyebrow/OND edits there, matching the pinned greps); honesty rules + footnote placement checks → Tasks 2/3/5; codex format review → Task 5; gated rollout + mirror → Task 6.
- **Placeholders:** none; every edit shows exact old/new strings; `<scratchpad>` is defined in Global Constraints.
- **Type consistency:** class names in Task 2/3 HTML exist in Task 1 CSS or the pre-existing stylesheet (`.metro-*` new; `.section-label`, `.domain-list/row/code/name/tag`, `.exam-banner`, `.note-muted`, `.chip`, `.topbar*`, `table` pre-existing). Station hrefs match the spec table exactly.
- **Known judgment calls recorded:** Lane-1 label carries the CE date so the relabeled `Periode N` headers stay unambiguous; `.code` column width handled by flex (no CSS change); k11's Basisinformatie period already correct, edit only adds cohort qualifier.
