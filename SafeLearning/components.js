// === MODULE DATA ===
const MODULES = [
  {
    cluster: 'Foundations',
    modules: [
      { id: 'landscape', num: '1', title: 'The Safe Learning Landscape', file: 'landscape.html',
        sections: [
          {name:'What "Safe" Means',id:'what-is-safety'},
          {name:'Three Traditions',id:'three-traditions'},
          {name:'Types of Guarantees',id:'guarantee-types'},
          {name:'Who\'s Who',id:'who-is-who'},
          {name:'Timeline of Landmark Papers',id:'timeline'},
          {name:'Notation for This Section',id:'notation'},
          {name:'Interactive: Constraint Semantics',id:'constraint-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'toolkit-lmi', num: '2', title: 'Math Toolkit I: Duality, LMIs & the S-Procedure', file: 'toolkit-lmi.html',
        sections: [
          {name:'Lagrangian Duality & KKT',id:'lagrangian-duality'},
          {name:'LMIs & Semidefinite Programs',id:'lmis-sdp'},
          {name:'The Schur Complement',id:'schur-complement'},
          {name:'The S-Procedure / S-Lemma',id:'s-procedure'},
          {name:'Quadratic Constraints',id:'quadratic-constraints'},
          {name:'Dissipativity & the KYP Lemma',id:'dissipativity'},
          {name:'Walkthrough: From a Quadratic Constraint to an LMI',id:'qc-to-lmi-walkthrough'},
          {name:'Interactive: S-Lemma in 2-D',id:'s-lemma-explorer'},
          {name:'Interactive: Lyapunov LMI Feasibility',id:'lmi-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'toolkit-gp', num: '3', title: 'Math Toolkit II: Kernels, GPs & Uncertainty Bounds', file: 'toolkit-gp.html',
        sections: [
          {name:'Kernels & the RKHS',id:'kernels-rkhs'},
          {name:'GP Regression = Kernel Ridge Regression',id:'gp-regression'},
          {name:'The Noise-Free Error Bound',id:'noise-free-bound'},
          {name:'Maximum Information Gain',id:'information-gain'},
          {name:'Frequentist Confidence Bounds & β_t',id:'confidence-bounds'},
          {name:'Practical and Rigorous Bounds (Fiedler, Scherer, Trimpe)',id:'practical-bounds'},
          {name:'When the Assumptions Fail',id:'misspecification'},
          {name:'Walkthrough: Deriving the RKHS Error Bound',id:'bound-walkthrough'},
          {name:'Interactive: GP Confidence Bands and β',id:'gp-band-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
    ]
  },
  {
    cluster: 'Safe Exploration (Trimpe lens)',
    modules: [
      { id: 'safe-bo', num: '4', title: 'Safe Bayesian Optimization: SafeOpt & Controller Tuning', file: 'safe-bo.html',
        sections: [
          {name:'The Safe BO Problem',id:'problem-setting'},
          {name:'SafeOpt: Safe Set, Expanders, Maximisers',id:'safeopt-algorithm'},
          {name:'What SafeOpt Guarantees',id:'safeopt-theory'},
          {name:'Practical Variants: SafeOpt-MC, StageOpt & Friends',id:'practical-variants'},
          {name:'BO for Controller Tuning (Trimpe group)',id:'controller-tuning'},
          {name:'Beyond SafeOpt: Constrained BO, Barriers, Information-Theoretic Safe Exploration',id:'beyond-safeopt'},
          {name:'Walkthrough: One SafeOpt Iteration',id:'safeopt-walkthrough'},
          {name:'Interactive: SafeOpt in 1-D',id:'safeopt-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'safe-bo-theory', num: '5', title: 'Is Safe BO Actually Safe? Real-β-SafeOpt and LoSBO', file: 'safe-bo-theory.html',
        sections: [
          {name:'The Gap Between Theory and Practice',id:'the-gap'},
          {name:'Real-β-SafeOpt',id:'real-beta'},
          {name:'LoSBO: Safety from a Lipschitz Constant Alone',id:'losbo'},
          {name:'LoS-GP-UCB: Dropping the Grid',id:'los-gp-ucb'},
          {name:'Multiple Constraints and Automotive Control',id:'mclosbo'},
          {name:'Event-Triggered and Time-Varying Safe BO',id:'time-varying'},
          {name:'Consequences for Control and Open Problems',id:'consequences'},
          {name:'Walkthrough: The LoSBO Safety Proof',id:'losbo-walkthrough'},
          {name:'Interactive: Break SafeOpt, Not LoSBO',id:'losbo-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'gosafe', num: '6', title: 'Global Safe Exploration of Dynamical Systems: GoSafe & GoSafeOpt', file: 'gosafe.html',
        sections: [
          {name:'Why Local Safe Exploration Gets Stuck',id:'why-local-fails'},
          {name:'Safety Along Trajectories',id:'dynamical-setting'},
          {name:'GoSafe: Exploring the Augmented Space',id:'gosafe'},
          {name:'GoSafeOpt: Backups from the Markov Property',id:'gosafeopt'},
          {name:'Safety and Optimality Guarantees',id:'guarantees'},
          {name:'Experiments and the β Caveat',id:'experiments'},
          {name:'Safe Exploration in MDPs: SafeMDP, SNO-MDP, ActSafe',id:'safe-mdp'},
          {name:'Walkthrough: Why Backups Keep You Safe',id:'backup-walkthrough'},
          {name:'Interactive: Local vs Global Safe Exploration',id:'gosafe-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'viability', num: '7', title: 'Viability & Safe Value Functions', file: 'viability.html',
        sections: [
          {name:'Failure Sets, Viable Sets and the Viability Kernel',id:'viability-kernel'},
          {name:'A Learnable Safety Measure',id:'safety-measure'},
          {name:'Penalising Failure: The Setup',id:'penalty-formulation'},
          {name:'Safe Value Functions: The Theorems',id:'safe-value-functions'},
          {name:'Viability of Future Actions and Entropy Regularisation',id:'entropy-robustness'},
          {name:'Uncertainty-Aware Safe RL at DSME (UPSi, Dyna-SAuR, CHEQ)',id:'uncertainty-aware'},
          {name:'Connections: Lagrangians, Reachability, Shields',id:'connections'},
          {name:'Walkthrough: Deriving the Penalty Threshold p*',id:'threshold-walkthrough'},
          {name:'Interactive: Penalty vs Safety on a Cliff Gridworld',id:'penalty-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
    ]
  },
  {
    cluster: 'Constrained Deep RL',
    modules: [
      { id: 'cmdp', num: '8', title: 'CMDPs, Duality & Lagrangian Methods', file: 'cmdp.html',
        sections: [
          {name:'Constrained MDPs',id:'cmdp-definition'},
          {name:'Occupancy Measures and the LP View',id:'occupancy-lp'},
          {name:'Lagrangian Relaxation and the Zero Duality Gap',id:'duality'},
          {name:'Primal-Dual Algorithms and Their Convergence',id:'primal-dual'},
          {name:'The Multiplier as a Controller: PID Lagrangians',id:'pid-lagrangian'},
          {name:'Risk-Sensitive Constraints: CVaR and Beyond',id:'risk-constraints'},
          {name:'Almost-Sure Constraints via State Augmentation',id:'state-augmentation'},
          {name:'Adjacent: Safe RLHF',id:'safe-rlhf'},
          {name:'Walkthrough: Dual Ascent on a Two-Action CMDP',id:'dual-walkthrough'},
          {name:'Interactive: Multiplier Dynamics (Plain vs PID)',id:'multiplier-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'policy-optimization', num: '9', title: 'Trust Regions, CPO & Modern Safe Policy Optimization', file: 'policy-optimization.html',
        sections: [
          {name:'The Performance Difference Lemma',id:'performance-difference'},
          {name:'Trust-Region Bounds for Return and Cost',id:'trust-region-bound'},
          {name:'Constrained Policy Optimization (CPO)',id:'cpo-update'},
          {name:'PCPO, FOCOPS, CUP, P3O, IPO, CVPO, C-TRPO',id:'projections-first-order'},
          {name:'Model-Based Safe RL: LAMBDA, SafeDreamer, ActSafe, SOOPER',id:'model-based'},
          {name:'Offline Safe RL: CPQ, COptiDICE, CDT, FISOR',id:'offline'},
          {name:'Benchmarks, Reproducibility and the 2026 State of the Art',id:'benchmarks'},
          {name:'Walkthrough: The CPO Step From Bound to Closed Form',id:'cpo-walkthrough'},
          {name:'Interactive: CPO vs Projection in Parameter Space',id:'cpo-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
    ]
  },
  {
    cluster: 'Control-Theoretic Safety',
    modules: [
      { id: 'barriers', num: '10', title: 'Barrier Functions, Reachability & Safety Filters', file: 'barriers.html',
        sections: [
          {name:'Forward Invariance and Nagumo\'s Theorem',id:'invariance-nagumo'},
          {name:'Control Barrier Functions',id:'cbf'},
          {name:'The CBF-QP Safety Filter and Its Closed Form',id:'cbf-qp'},
          {name:'High Relative Degree: ECBFs and HOCBFs',id:'high-order'},
          {name:'Robust CBFs, ISSf and Learned Residuals',id:'robust-cbf'},
          {name:'Hamilton–Jacobi Reachability',id:'hj-reachability'},
          {name:'Predictive Safety Filters (Wabersich & Zeilinger)',id:'predictive-safety-filter'},
          {name:'Shields and the Unified Safety-Filter View',id:'shielding-unified'},
          {name:'Learned and Uncertainty-Aware Filters (incl. UPSi)',id:'learned-filters'},
          {name:'Walkthrough: From the CBF Condition to the Filtered Input',id:'kkt-walkthrough'},
          {name:'Interactive: CBF-QP Safety Filter on a Robot',id:'cbf-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'lyapunov-mpc', num: '11', title: 'Lyapunov Certificates, Safe Model-Based RL & Learning-Based MPC', file: 'lyapunov-mpc.html',
        sections: [
          {name:'Lyapunov Stability and Regions of Attraction',id:'lyapunov-roa'},
          {name:'Safe Model-Based RL with Stability Guarantees (Berkenkamp et al.)',id:'berkenkamp-2017'},
          {name:'Lyapunov-Based Safe RL (Chow et al.)',id:'lyapunov-safe-rl'},
          {name:'Neural Lyapunov, Barrier and Contraction Certificates',id:'neural-certificates'},
          {name:'Learning-Based and Robust MPC',id:'learning-based-mpc'},
          {name:'Certified Approximate MPC with Neural Networks',id:'certified-approx-mpc'},
          {name:'Statistical Guarantees Meet Robust Control (Fiedler, Scherer, Trimpe)',id:'statistical-robust-synthesis'},
          {name:'Walkthrough: Certifying a Region of Attraction from Samples',id:'roa-walkthrough'},
          {name:'Interactive: Certified ROA Under Model Uncertainty',id:'roa-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
    ]
  },
  {
    cluster: 'Certified Neural Networks (Pauli lens)',
    modules: [
      { id: 'lipsdp', num: '12', title: 'Lipschitz Bounds via SDP: LipSDP and Beyond', file: 'lipsdp.html',
        sections: [
          {name:'Lipschitz Constants and Certified Robustness',id:'lipschitz-robustness'},
          {name:'The Product Bound and Why It Is Loose',id:'naive-bound'},
          {name:'Slope Restriction as an Incremental Quadratic Constraint',id:'slope-restriction-qc'},
          {name:'The LipSDP Derivation',id:'lipsdp-derivation'},
          {name:'What Went Wrong With Coupled Multipliers',id:'lipsdp-network-error'},
          {name:'Training Under Lipschitz Constraints: ADMM and Barriers (Pauli et al.)',id:'training-with-lipsdp'},
          {name:'CNNs as Dynamical Systems: 1-D, Roesser and GLipSDP',id:'cnn-state-space'},
          {name:'Beyond Slope Restriction: GroupSort, MaxMin, Householder',id:'beyond-slope-restricted'},
          {name:'Scalable Variants and Hardness Results',id:'scalability'},
          {name:'Walkthrough: LipSDP for One Hidden Layer',id:'lipsdp-walkthrough'},
          {name:'Interactive: Naive vs LipSDP vs Empirical',id:'lipsdp-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'lipschitz-by-design', num: '13', title: 'Lipschitz-by-Design Networks & Direct Parameterizations', file: 'lipschitz-by-design.html',
        sections: [
          {name:'Constrain or Parameterize?',id:'why-by-design'},
          {name:'Spectral Normalization, Parseval, Cayley, SOC, AOL',id:'orthogonal-layers'},
          {name:'SLL and Sandwich Layers: LMIs Solved by Construction',id:'sll-sandwich'},
          {name:'Lipschitz-Bounded CNNs: Cayley–Gramian and LipKernel (Pauli et al.)',id:'cnn-parameterizations'},
          {name:'Recurrent Equilibrium Networks and R2DN',id:'rens'},
          {name:'Certified Robust Accuracy: State of the Art 2026',id:'certified-sota'},
          {name:'Walkthrough: Deriving the Sandwich Layer From the LMI',id:'sandwich-walkthrough'},
          {name:'Interactive: Cayley Transform and a 1-Lipschitz Layer',id:'cayley-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'nn-in-the-loop', num: '14', title: 'Neural Networks in the Loop: QCs, IQCs & Dissipativity', file: 'nn-in-the-loop.html',
        sections: [
          {name:'The Feedback Setup and Loop Transformations',id:'feedback-setup'},
          {name:'Local Sector QCs and the Stability LMI (Yin, Seiler, Arcak)',id:'local-sector-qc'},
          {name:'Dynamic Multipliers: Acausal Zames–Falb (Pauli et al.)',id:'zames-falb'},
          {name:'Offset-Free Setpoint Tracking With NN Controllers (Pauli et al.)',id:'offset-free'},
          {name:'Dissipativity Analysis and Training of RNNs (Pauli et al.)',id:'dissipativity-rnn'},
          {name:'Synthesis With Guarantees: Dissipativity-Constrained RL and Youla-REN',id:'synthesis'},
          {name:'Reachability of NN Loops and Verified Lyapunov Controllers',id:'reachability-verification'},
          {name:'Towards Scale: ReLU IQCs and Incremental Analysis (2025–2026)',id:'scalable-2026'},
          {name:'Walkthrough: Stability LMI for a Linear Plant With a One-Layer NN',id:'loop-walkthrough'},
          {name:'Interactive: A Neural Controller in Closed Loop',id:'loop-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
      { id: 'verification', num: '15', title: 'Verification & Distribution-Free Guarantees', file: 'verification.html',
        sections: [
          {name:'The Verification Problem',id:'verification-problem'},
          {name:'Bound Propagation: IBP, CROWN, α,β-CROWN',id:'bound-propagation'},
          {name:'SDP Relaxations of Verification',id:'sdp-relaxation'},
          {name:'Randomized Smoothing',id:'randomized-smoothing'},
          {name:'Conformal Prediction for Safe Planning and Control',id:'conformal-prediction'},
          {name:'The Scenario Approach',id:'scenario-approach'},
          {name:'Deterministic vs Probabilistic Guarantees: A Comparison',id:'comparison'},
          {name:'Walkthrough: IBP vs CROWN on a Two-Neuron Network',id:'crown-walkthrough'},
          {name:'Interactive: Output Bounds and Conformal Coverage',id:'bounds-explorer'},
          {name:'Exercises',id:'exercises'},
          {name:'Key Papers',id:'papers'},
          {name:'Flashcards',id:'flashcards'},
        ] },
    ]
  },
  {
    cluster: 'Reference',
    modules: [
      { id: 'formulas', num: '∑', title: 'Formula Sheet', file: 'formulas.html',
        sections: [
        ] },
      { id: 'papers', num: '¶', title: 'Paper Atlas', file: 'papers.html',
        sections: [
        ] },
    ]
  },
];

// === SIDEBAR ===
function renderSidebar(activeModuleId) {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  let html = '<div class="sidebar-title"><span>Safe Learning</span><button class="sidebar-toggle" onclick="toggleSidebar()" title="Hide sidebar">&times;</button></div>';

  MODULES.forEach(cluster => {
    html += '<div class="sidebar-cluster">' + cluster.cluster + '</div>';
    cluster.modules.forEach(mod => {
      const isActive = mod.id === activeModuleId;
      html += '<a href="' + mod.file + '" class="sidebar-link' + (isActive ? ' active' : '') + '">' + mod.num + '. ' + mod.title + '</a>';
      if (isActive && mod.sections.length > 0) {
        mod.sections.forEach(sec => {
          var name = typeof sec === 'string' ? sec : sec.name;
          var anchor = typeof sec === 'string' ? sec.toLowerCase().replace(/[^a-z0-9]+/g, '-') : sec.id;
          html += '<a href="#' + anchor + '" class="sidebar-subsection">' + name + '</a>';
        });
      }
    });
  });

  sidebar.innerHTML = html;

  if (localStorage.getItem('sidebar-collapsed') === 'true') {
    sidebar.classList.add('collapsed');
  }
}

function toggleSidebar() {
  const sidebar = document.getElementById('sidebar');
  sidebar.classList.toggle('collapsed');
  localStorage.setItem('sidebar-collapsed', sidebar.classList.contains('collapsed'));
}

// === MATH RENDERING ===
function renderMath(el) {
  if (typeof renderMathInElement === 'function') {
    renderMathInElement(el, {
      delimiters: [
        {left: '$$', right: '$$', display: true},
        {left: '$', right: '$', display: false}
      ]
    });
  }
}

// === COLLAPSIBLE SECTIONS ===
function initCollapsibles() {
  document.querySelectorAll('.collapsible-header').forEach(header => {
    header.addEventListener('click', () => {
      header.parentElement.classList.toggle('open');
    });
  });
}

// === FLASHCARD ENGINE ===
function initFlashcards(containerId, cards) {
  const container = document.getElementById(containerId);
  if (!container || cards.length === 0) return;

  const storageKey = 'flashcards-' + containerId;
  let state = JSON.parse(localStorage.getItem(storageKey) || '{}');
  let currentIndex = 0;
  let revealed = false;

  function getCorrectCount() { return Object.values(state).filter(v => v > 0).length; }

  function render() {
    const card = cards[currentIndex];
    const correct = getCorrectCount();
    container.innerHTML =
      '<div class="flashcard-counter">' + (currentIndex + 1) + ' / ' + cards.length + ' &mdash; ' + correct + ' mastered</div>' +
      '<div class="flashcard">' +
        '<div class="flashcard-question">' + card.q + '</div>' +
        '<div class="flashcard-answer' + (revealed ? ' visible' : '') + '">' + card.a + '</div>' +
        (!revealed ? '<button class="flashcard-reveal" onclick="revealFlashcard(\'' + containerId + '\')">Show answer</button>' : '') +
      '</div>' +
      (revealed ?
        '<div class="flashcard-buttons">' +
          '<button class="flashcard-btn again" onclick="flashcardRate(\'' + containerId + '\', false)">Again</button>' +
          '<button class="flashcard-btn got-it" onclick="flashcardRate(\'' + containerId + '\', true)">Got it</button>' +
        '</div>' : '') +
      '<div class="flashcard-progress">' + correct + ' / ' + cards.length + ' cards mastered</div>';
    renderMath(container);
  }

  container._state = {
    cards: cards,
    currentIndex: function() { return currentIndex; },
    setIndex: function(i) { currentIndex = i; revealed = false; },
    reveal: function() { revealed = true; },
    rate: function(correct) {
      state[currentIndex] = correct ? 1 : 0;
      localStorage.setItem(storageKey, JSON.stringify(state));
    },
    render: render
  };
  render();
}

function revealFlashcard(containerId) {
  const s = document.getElementById(containerId)._state;
  s.reveal();
  s.render();
}

function flashcardRate(containerId, correct) {
  const s = document.getElementById(containerId)._state;
  s.rate(correct);
  var next = (s.currentIndex() + 1) % s.cards.length;
  s.setIndex(next);
  s.render();
}

// === STEP-BY-STEP WALKTHROUGH ===
function initWalkthrough(containerId, steps) {
  const container = document.getElementById(containerId);
  if (!container || steps.length === 0) return;

  let currentStep = 0;

  function render() {
    const step = steps[currentStep];
    let tabsHtml = steps.map(function(s, i) {
      return '<div class="walkthrough-step-tab' + (i === currentStep ? ' active' : '') + '" onclick="walkthroughGoTo(\'' + containerId + '\', ' + i + ')">' + s.tab + '</div>';
    }).join('');

    container.innerHTML =
      '<div class="interactive-label">' + (container.dataset.title || 'Walkthrough') + '</div>' +
      '<div class="walkthrough-steps">' + tabsHtml + '</div>' +
      '<div class="walkthrough-content">' +
        '<h3 class="subsection-heading">' + step.title + '</h3>' +
        '<p style="margin: 8px 0 14px; font-size: 14px; color: #444;">' + step.text + '</p>' +
        (step.visual || '') +
        (step.insight ? '<div class="insight-box"><div class="box-label">Key insight</div><div>' + step.insight + '</div></div>' : '') +
      '</div>' +
      '<div class="walkthrough-nav">' +
        '<button onclick="walkthroughGoTo(\'' + containerId + '\', ' + (currentStep - 1) + ')"' + (currentStep === 0 ? ' disabled' : '') + '>&larr; Previous</button>' +
        '<button onclick="walkthroughGoTo(\'' + containerId + '\', ' + (currentStep + 1) + ')"' + (currentStep === steps.length - 1 ? ' disabled' : '') + '>Next &rarr;</button>' +
      '</div>';
    renderMath(container);
  }

  container._walkthrough = {
    goTo: function(i) {
      currentStep = Math.max(0, Math.min(steps.length - 1, i));
      render();
    }
  };
  render();
}

function walkthroughGoTo(containerId, step) {
  document.getElementById(containerId)._walkthrough.goTo(step);
}

// === INIT ===
// initCollapsibles() is called explicitly in each page's inline script
// to avoid double-registration when both DOMContentLoaded and inline fire.
