# SafeLearning page contract (read fully before writing)

Pages live in `~/SafetyBased/SafeLearning/` (source of truth; deploy to `~/Dropbox/ploxkevin.github.io/SafeLearning/` with rsync, see README): interactive study/research notes on safe RL,
safe learning-based control and certified neural networks. They must look and read exactly like Kevin's existing
study-note sections. Style references (skim before writing):

- `/home/oxrexkevin/Dropbox/ploxkevin.github.io/7S1B20/buckling.html` (derivation walkthrough, collapsible derivations, explorer, flashcards)
- `/home/oxrexkevin/Dropbox/ploxkevin.github.io/2IX30/part8.html` (definition boxes, tables, explorer, exercises with `<details>`)
- any finished SafeLearning module, e.g. `SafeLearning/lipsdp.html` or `SafeLearning/safe-bo-theory.html`
- `SafeLearning/components.js` (MODULES: your page id and section ids) and `SafeLearning/style.css` (all classes you may use)

Write ONLY the file(s) you are assigned. Do not modify style.css, components.js or index.html unless told to. Do not run git.

## 1. File skeleton

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="UTF-8">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>{NUM}. {TITLE} — Safe Learning</title>
  <link rel="stylesheet" href="style.css">
  <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
  <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
  <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js"
    onload="renderMathInElement(document.body, {delimiters: [{left: '$$', right: '$$', display: true}, {left: '$', right: '$', display: false}]});"></script>
</head>
<body>

  <nav id="sidebar" class="sidebar"></nav>
  <button class="sidebar-open" onclick="toggleSidebar()">&#9776;</button>

  <main class="main-content">

    <h1 class="page-title">{NUM}. {TITLE}</h1>
    <p class="page-subtitle">{SUBTITLE}</p>

    <div class="prereq-box"> ... </div>   <!-- "Before you start" (see §7) -->

    <div class="page-toc">
      <div class="page-toc-title">Contents</div>
      <a href="#{section-id}">1. {Section name}</a>
      ...
      <a class="toc-interactive" href="#{explorer-section-id}">Interactive: {Explorer name}</a>
      <a href="#exercises">Exercises</a>
      <a href="#reading">Further Reading</a>          <!-- primers; modules use #papers "Key Papers" -->
      <a class="toc-interactive" href="#flashcards">Flashcards</a>
    </div>

    <h2 class="section-heading" id="{section-id}">1. {Section name}</h2>
    ...
    <h2 class="section-heading" id="exercises">Exercises</h2>
    ...
    <h2 class="section-heading" id="flashcards">Flashcards</h2>
    <div class="flashcard-container" id="{prefix}-flashcards"></div>

    <div class="page-nav">
      <a href="{prev}.html">&larr; {Prev title}</a>
      <a href="{next}.html">{Next title} &rarr;</a>
    </div>

  </main>

  <script src="components.js"></script>
  <script>
    renderSidebar('{page-id}');
    initCollapsibles();
    initWalkthrough('{prefix}-walkthrough', [ ... ]);
    initFlashcards('{prefix}-flashcards', [ ... ]);
    // explorer IIFEs go here, AFTER components.js (they may call renderMath)
  </script>
</body>
</html>
```

The section ids and their order MUST match the page's `sections` array in `SafeLearning/components.js`.

## 2. Components (existing classes only)

- **Definition / theorem / key equation** → `<div class="definition-box"><div class="box-label">Definition &mdash; Positive semidefinite matrix</div><div>...</div></div>`.
  Labels: "Definition — X", "Theorem — X", "Lemma — X", "Fact — X", "Key equation — X", "Notation — X".
- **Intuition / why it matters / where used** → `insight-box` (labels: "Intuition", "Why it matters", "Where this is used", "Connection to Module N").
- **Pitfalls** → `warning-box` (labels: "Pitfall", "Common mistake", "Caveat").
- **Proofs, longer derivations, worked examples** → collapsible:
  `<div class="collapsible"><div class="collapsible-header">Proof — ...</div><div class="collapsible-body">...</div></div>`
  (headers: "Proof —", "Derivation —", "Worked example —", "Going deeper —", "Background —" for prerequisite explanations; give every header a topic, never a generic "the missing step"). Nested collapsibles work (the CSS opens only a box's own body) but prefer one level.
- **Step-by-step derivation** → walkthrough:
  `<div class="interactive-container" id="{prefix}-walkthrough" data-title="Derivation: ..."></div>` +
  `initWalkthrough('{prefix}-walkthrough', [{tab: '1. Setup', title: 'Step 1: ...', text: '...', visual: '<div class="math-block">$$...$$</div>', insight: '...'}, ...])` (4–7 steps; several walkthroughs allowed with different ids).
- **Display math** → `<div class="math-block">$$ ... $$</div>`; inline `$...$`. A wide inline formula that cannot wrap: `<span class="math-scroll">$...$</span>`.
- **Pseudocode** → `<div class="algorithm"><div class="algorithm-title">Algorithm 1: ...</div><ol><li>...</li></ol></div>`.
- **Citations** → `<a class="cite" href="{url}" target="_blank" rel="noopener">Author et al., Venue Year</a>`. Never invent a reference; verify title/authors/year/URL (WebFetch) before citing anything new.
- **Tables** → plain `<table><thead>…</thead><tbody>…</tbody></table>`.
- **Cross-links** → `<a href="{file}.html#{section-id}">Primer A</a>` / `<a href="lipsdp.html#lipsdp-derivation">Module 12</a>` (ids from components.js only).
- **Exercises** (`id="exercises"`), each with a full worked solution, exactly this pattern:

```html
<details style="margin-bottom:14px;border:1px solid #d0d8ea;border-radius:6px;overflow:hidden;">
  <summary style="padding:12px 16px;background:#f0f4fb;cursor:pointer;font-weight:600;font-size:14px;">
    Exercise {N}.1 &mdash; {Title}
  </summary>
  <div style="padding:14px 16px;font-size:14px;">
    <p style="margin-top:0;">{Question}</p>
    <details style="margin-top:10px;">
      <summary style="cursor:pointer;color:#2d5fa6;font-weight:600;">Show answer</summary>
      <div style="margin-top:8px;padding:10px 14px;background:#f7f9fc;border-left:3px solid #2d5fa6;border-radius:0 4px 4px 0;">
        {Worked solution}
      </div>
    </details>
  </div>
</details>
```

- **Flashcards**: `{q: '...', a: '...'}` objects; math allowed.

## 3. Interactive explorers

Section `<h2 class="section-heading" id="{explorer-id}">Interactive: {Name}</h2>`, one intro sentence, then
`<div class="interactive-container"><div class="interactive-label">{Name}</div> ... </div>`. Controls: `.slider-group` /
`.slider-control` with `<label>Name <span id="..">value</span></label>` + `<input type="range">`; readouts in a small panel;
plots as inline `<svg viewBox=...>` with `style="display:block;max-width:100%;border:1px solid #e0e0e0;border-radius:6px;background:#fff;"`.
Vanilla JS IIFE after components.js; real computations (not cartoons); seeded PRNG (mulberry32) where randomness is used;
call `renderMath(el)` after writing math into the DOM; must work at 390 px width (viewBox + max-width:100%, flex rows wrap).
Palette: blue `#1565c0`/`#2d5fa6`, orange `#e67e22`, teal `#00838f`, purple `#7b1fa2`, green `#2e7d32`, red `#c62828`, blue-grey `#455a64` (primers), greys.

## 4. Math and escaping rules (pages are linted in headless Chromium)

- KaTeX 0.16.9 only: `aligned`, `cases`, `pmatrix`, `bmatrix`, `array`, `\operatorname*{arg\,max}`; `\boldsymbol` not `\bm`; no `\newcommand`, `\label`, `\eqref`, `\tag`.
- HTML trap: never a raw `<` directly before a letter inside math (`$a<b$` becomes a tag): write `\lt`, `\le` or `a < b` with spaces.
- No literal dollar signs in prose.
- JS strings (walkthrough/flashcards): double every backslash (`\\frac`), escape `'` as `\'`, keep strings on one line (use `+`).
- Define every symbol before use; consistent notation with the notation table on `landscape.html#notation`.
- Theorems: precise statement with ALL assumptions → "in words" → why each assumption matters. Faithful to sources.

## 5. Voice and depth

Direct, compact, explanatory; short paragraphs; intuition first, formalism second, interpretation after; never skip
algebra in derivations; explain the reason for each step. English, no emojis.

## 6. Self-check before finishing (mandatory)

```
cd ~/SafetyBased/qa && node check.mjs ../SafeLearning/{file}.html
```

The report must show no consoleErrors,
pageErrors, leftoverDollar, katexErrors, missingAnchors, brokenLinks, and mobileOverflow false (if true,
`mobileOverflowCause` names the culprit). Links to primer pages that are being written concurrently are acceptable if they
use the planned anchors. Look at the screenshot in `qa/shots/{file}.png` (Read tool) to confirm the explorer renders.

## 7. The "Before you start" box (every module and primer)

Right after the page subtitle:

```html
<div class="prereq-box">
  <div class="prereq-title">Before you start</div>
  <p style="margin:0;">This module assumes: </p>
  <ul>
    <li><a href="primer-linalg.html#la-psd">Positive semidefinite matrices &amp; quadratic forms</a> <span class="prereq-src">(Primer A)</span></li>
    <li><a href="toolkit-lmi.html#s-procedure">The S-procedure</a> <span class="prereq-src">(Module 2)</span></li>
  </ul>
</div>
```

4–10 items, most important first; only primers and EARLIER modules. Primers list the baseline they assume
(first-course linear algebra + single-variable calculus) and earlier primers.

## 8. PRIMER pages (A–E) — additional rules

- Audience: a student who has just finished one first course in linear algebra plus single-variable calculus. Start from
  what they know, build each concept with a tiny numeric example and (where possible) a picture, then state it in general.
- Every concept gets: a definition box → intuition → worked numeric example → the general statement (short proofs in full,
  longer ones as a proof sketch in a collapsible) → an insight-box "Where this is used" linking to the exact module
  sections that need it (the audit lists them) → a pitfall if there is a common one.
- Scope: cover every concept the audit maps to your sections (nothing a later module needs may be missing), but stay a
  primer: no research-level detours. Advanced results that modules only cite (e.g. self-normalized martingale bounds,
  viscosity solutions) get a precise statement + intuition + a pointer, not a proof.
- Structure: the section list in components.js (ends with exercises, reading, flashcards); at least one step-by-step
  walkthrough; one explorer with real computations; 6–8 exercises with worked solutions (easy → harder; recompute every
  number); 12–16 flashcards; a "Further Reading" table (textbooks and tutorials, verified URLs) instead of Key Papers.
- Size: 60–120 KB.

## Reader review updates (October 2026)

The expanded learning material supersedes the original 6–8 exercise and 60–120 KB targets above. Preserve existing
problems and section IDs. Every substantive primer section has Easy, Medium and Hard practice; every research module
has at least twelve graded problems (four per level) before its original research exercises. Each new problem has a
separate hint, a full solution that explains the reasoning, and exact review links.

Control reading load with clear first-reading routes, local practice menus and named collapsibles for optional proofs
and technical background. After shared navigation or CSS changes, run `node qa/learning_review.mjs` from the repository
root; it checks 320, 390, 768, 820 and 1280 px, including expanded content and keyboard/mobile interactions.

## Book application material (2026-10-08)

The application labs are authored in `book/chapters/{page}.html` and integrated
by `python3 book/build.py`. Edit those fragments rather than the marked
`BOOK APPLICATION` blocks in the generated teaching pages. Preserve all earlier
theory, exercises, IDs and interactive scripts. Each lab states learning
objectives, a hypothetical decision model with units and assumptions, worked
reasoning, application exercises with separate hints and full solutions, and a
chapter review/bridge. Native `<details>` use the shared book styles; do not put
their bodies in `.collapsible-body`, which belongs to the JavaScript component.

`book/frontmatter.html`, `book/case-studies.html` and `book/glossary.html` generate
three reference pages. Their structure differs from the research-module graded
practice layout. `book/validate.py` checks these pages, the integrated fragments,
all local links and exact preservation of the original teaching pages. It does
not replace rendered QA. The shared print handlers open disclosure bodies for
printing and restore their previous state afterward; confirm this in an actual
browser when the environment permits it.

Keep proof coverage explicit. Only statements mapped in the coverage records
are formalized; physical model validity and statistical assumptions remain
separate obligations. Recompute the relevant authored examples and run the
pinned Lean audit after mathematical changes. Store new audit evidence separately
from historical source revisions.
