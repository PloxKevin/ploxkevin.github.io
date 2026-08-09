# iFEM Interactive Study Guide — Design

Date: 2026-08-04 (built 2026-08-04 → 2026-08-09)
Status: built, QA-clean, cross-agent reviewed
Author: Claude Code (autonomous, commissioned by Kevin); curriculum
critiqued and pages adversarially reviewed by Codex CLI.

## Goal

A study guide at `https://ploxkevin.github.io/iFEM/` on the **inverse
Finite Element Method**, in the same style and ideology as the 5LSH0
guide: prerequisites-first, complexity-ascending, interactive,
flashcard-reinforced. Scope runs from continuum-mechanics/FEM
prerequisites through the canonical Tessler–Spangler iFEM shape-sensing
formulation, the wider inverse-FEM family (material identification, load
reconstruction, reference-configuration recovery), up to adjoint /
differentiable / learning-based methods and digital twins (2023–2026).

## Why this shape

- Kevin's PhD is vision-based tactile sensing / soft robot skin;
  inverse-FEM force reconstruction from measured deformation is directly
  adjacent, so the guide doubles as PhD substrate.
- "iFEM" canonically means Tessler & Spangler's inverse Finite Element
  Method (shape sensing from discrete strains). A guide covering only
  that would miss the broader inverse-problem toolchain the recent
  literature builds on. Both are covered — and, per the Codex consult,
  kept explicitly distinct rather than blurred into one family.

## Site architecture (mirrors 5LSH0)

```
iFEM/
  index.html      landing: back-link, landing-header, D3 topic map
                  (clickable, cluster-coloured, prereq/shared edges),
                  module list grouped by cluster
  style.css       5LSH0 stylesheet + a .ref-list block (5LSH0 cites no
                  literature; a literature-built guide must)
  components.js   the 5LSH0 engine verbatim (sidebar, flashcards,
                  walkthrough, collapsibles, KaTeX re-render) with an
                  iFEM MODULES registry: 126 sections across 12 modules
  mod1..mod12.html
```

Page anatomy per 5LSH0/mod7.html: KaTeX 0.16.9 CDN · sidebar ·
page-title/subtitle · page-toc (sections + italic interactive entries +
Flashcards) · `h2.section-heading` anchors · definition-box (incl. a
"Core Problem" box) · insight-box · collapsible derivations ·
interactive-container widgets · walkthrough · flashcards · References ·
prev/next nav.

**Figures:** every diagram is hand-drawn inline SVG (7S1B20 style). No
PNGs, no `<img>` tags — self-contained, copyright-clean, and parametric
where that teaches better.

## Curriculum (as built, after the Codex consult)

**A. Foundations** (#1565c0)
1. Continuum Mechanics Primer — kinematics, $\mathbf{F}$/$J$/polar
   decomposition, small vs Green–Lagrange strain, work-conjugate stress
   pairs, linear elasticity, Voigt & the factor-of-2 shear trap, plane
   stress/strain, compatibility, hyperelasticity.
2. The Forward FEM — weak form, virtual work, shape functions,
   isoparametric mapping, quadrature, B-matrix, assembly, $\mathbf{KU=F}$,
   patch test, shear locking, beam/plate kinematics, section strains.
3. Inverse Problems & Regularization — Hadamard, least squares, SVD,
   discrete Picard, Tikhonov, TSVD, parameter choice, Bayesian view, and
   the taxonomy that frames the whole guide.

**B. Core iFEM — shape sensing** (#e67e22)
4. The iFEM Principle — Tessler–Spangler weighted least squares;
   material-free/load-free scope; Ko & modal methods as a comparison box.
5. iFEM Elements — inverse Timoshenko beam, iMIN3, iQS4, RZT.
6. Sensors, Placement & Deployment — gauges, FBG, rosette transforms,
   placement, sparse sensing, SEA pre-extrapolation, weighting.

**C. The wider inverse-FEM family** (#00838f) — sibling branches that
require only Foundations, *not* modules 4–6
7. Material Identification — FEMU, VFM, DIC, elastography.
8. Load & Contact Force Reconstruction — influence matrices, regularized
   inversion, tactile/GelSlim case study.
9. Reference Configuration & Prestress — inverse elastostatics,
   Sellier iteration, prestress, nonuniqueness.

**D. Modern developments** (#7b1fa2)
10. Adjoints & Differentiable FEM — objectives, direct sensitivities,
    adjoints, unrolled vs implicit AD, differentiable solvers.
11. Learning-Enhanced Inversion — organised by insertion point: sensor
    completion/virtual strains, priors, surrogates, residual correction,
    placement, amortized inversion (PINNs vs neural operators).
12. Digital Twins & Frontiers — assimilation, uncertainty, latency, the
    model→shadow→twin ladder, soft-robot proprioception.

**Framing spine:** module 3 introduces the observation model
$y = \mathcal{H}(u, p, f, X_0) + b + \eta$ and the discipline of asking,
for every method: what is measured, what is unknown, what is assumed
known, what is unobservable. Every main interactive carries a persistent
panel — measurements / unknowns / assumptions / rank-or-conditioning /
validation error.

## How it was built

1. **Curriculum consult (Codex).** Restructured the draft: modules 7–9
   became sibling branches; 10/11 swapped so gradients precede learning;
   module 9 renamed; module 12 reframed from applications gallery to
   assimilation capstone. It also caught a false claim in this document's
   first draft ("adjoint ≈ regularized least squares" — regularization
   changes the objective; an adjoint computes its gradient).
2. **Research + adversarial verification (24 agents).** One researcher per
   module, each required to confirm every reference on the live web and
   record the evidence URL; then an *independent* verifier per module
   re-checked every citation and equation and wrote the amended brief.
   Separation of duties caught, among others, a fabricated retraction
   claim, a cross-page sign-convention clash, and several numeric errors.
3. **Completeness critic** over the whole curriculum → deduplication
   rulings (canonical homes for surface→section strain, weighted iFEM,
   sensor placement, SVD/Tikhonov, RZT, elastography).
4. **Page build (12 agents)** under a binding style contract: content only
   from the verified brief, references verbatim, every Codex trap
   addressed.
5. **QA.** Deterministic checks: TOC↔anchor integrity, registry validity,
   prev/next chain, KaTeX hygiene, JS syntax of every inline block, and a
   provenance check matching every printed reference against the verified
   briefs. Result: 0 blockers / 0 major / 0 minor.
6. **Cross-model adversarial review (Codex)** of the built pages before
   publication.

## Provenance discipline

Proposers never verify their own claims. Every reference on every page
traces to a brief entry confirmed on the live web, or to
`refcheck_extras.json` (independently verified). Three references that a
builder pulled from a stale pre-verification backup were caught by the
provenance check and individually re-verified before being kept.

## Known gaps (honest)

- `mod12.html` has no step-through walkthrough widget (its builder hit a
  quota limit; the page was closed out by hand from its verified brief).
  It still carries three interactives and full flashcards.
- Deliberately out of scope, flagged rather than faked: geometrically
  nonlinear/large-deformation iFEM, 3D solid inverse elements,
  heterogeneous sensor fusion, formal UQ of the reconstructed field, and
  benchmark datasets.

## Build artefacts

Working root `~/ifem-build/` (durable — the session `/tmp` scratchpad was
wiped mid-project and the pages had to be reconstructed by replaying the
subagent transcripts): `briefs/` verified content briefs,
`refcheck_extras.json` verified extra references, `qa.py` the
deterministic QA harness, `codex-review.md` the adversarial review.
