// === MODULE DATA ===
const MODULES = [
  {
    cluster: "Foundations",
    modules: [
      { id: 'mod1', num: '1', title: "Continuum Mechanics Primer", file: 'mod1.html',
        sections: [
          {name:"Why Continuum Mechanics Before iFEM",id:"why-continuum-mechanics-for-ifem"},{name:"Configurations, Motion, and Displacement",id:"configurations-and-displacement"},{name:"The Deformation Gradient F",id:"deformation-gradient"},{name:"Strain Measures: Small Strain vs Green\u2013Lagrange",id:"strain-measures"},{name:"Compatibility: When Is a Strain Field Integrable?",id:"compatibility"},{name:"Stress Measures: Cauchy, First and Second Piola\u2013Kirchhoff",id:"stress-measures"},{name:"Linear Elasticity and the Hooke Tensor",id:"linear-elasticity"},{name:"Voigt Notation and the Factor-of-2 Shear Trap",id:"voigt-notation"},{name:"Plane Stress and Plane Strain",id:"plane-stress-plane-strain"},{name:"Hyperelasticity: Stress From a Strain-Energy Density",id:"hyperelasticity-strain-energy"},{name:"Neo-Hookean, Mooney\u2013Rivlin, and Incompressibility",id:"neo-hookean-mooney-rivlin"},{name:"Choosing the Right Theory: A Decision Guide",id:"choosing-the-right-theory"}
        ] },
      { id: 'mod2', num: '2', title: "The Forward Finite Element Method", file: 'mod2.html',
        sections: [
          {name:"From Strong Form to Weak Form",id:"strong-form-to-weak-form"},{name:"Virtual Work and Minimum Potential Energy",id:"virtual-work-minimum-potential-energy"},{name:"Discretization: Shape Functions",id:"shape-functions-discretization"},{name:"Isoparametric Mapping and Gauss Quadrature",id:"isoparametric-mapping-gauss-quadrature"},{name:"The B-Matrix and Element Stiffness",id:"b-matrix-element-stiffness"},{name:"Assembly, Boundary Conditions, and Solving KU = F",id:"assembly-boundary-conditions-solving"},{name:"Convergence and the Patch Test",id:"convergence-patch-test"},{name:"Beam Kinematics: Euler-Bernoulli vs Timoshenko",id:"beam-kinematics-euler-bernoulli-timoshenko"},{name:"Plate Kinematics: Kirchhoff vs Reissner-Mindlin",id:"plate-kinematics-kirchhoff-reissner-mindlin"},{name:"Shear Locking: Mechanism and Cures",id:"shear-locking"},{name:"Section Strains: The Bridge to iFEM",id:"section-strains-ifem-bridge"}
        ] },
      { id: 'mod3', num: '3', title: "Inverse Problems & Regularization", file: 'mod3.html',
        sections: [
          {name:"Forward vs. Inverse: Which Direction Is Hard?",id:"forward-vs-inverse"},{name:"The Observation Model: One Equation, Four Families",id:"observation-model"},{name:"Hadamard Well-Posedness and Why Elasticity Inversion Breaks It",id:"hadamard-well-posedness"},{name:"Linear Least Squares and the Normal Equations",id:"least-squares-normal-equations"},{name:"The SVD: Anatomy of an Ill-Conditioned Problem",id:"svd-ill-conditioning"},{name:"The Discrete Picard Condition",id:"discrete-picard-condition"},{name:"Tikhonov Regularization",id:"tikhonov-regularization"},{name:"Truncated SVD and Friends",id:"truncated-svd"},{name:"Choosing the Regularization Parameter",id:"choosing-the-parameter"},{name:"Nonlinear Problems: Gauss\u2013Newton and Levenberg\u2013Marquardt",id:"gauss-newton-lm"},{name:"The Bayesian View: Regularization as a Prior",id:"bayesian-view"},{name:"A Taxonomy of Inverse Problems in Solid Mechanics",id:"taxonomy-solid-mechanics"},{name:"Practical Workflow: Diagnosing and Solving Your Inverse Problem",id:"practical-workflow"}
        ] },
    ]
  },
  {
    cluster: "Core iFEM \u2014 Shape Sensing",
    modules: [
      { id: 'mod4', num: '4', title: "The iFEM Principle", file: 'mod4.html',
        sections: [
          {name:"Why Shape Sensing: The Helios Lesson",id:"why-shape-sensing"},{name:"Forward vs Inverse: What Makes Shape Sensing Hard",id:"forward-vs-inverse"},{name:"Kinematic Scaffold: First-Order Shear Deformation Theory",id:"fsdt-kinematics"},{name:"From Surface Strains to Section Strains",id:"section-strains-from-sensors"},{name:"The Tessler\u2013Spangler Functional",id:"the-variational-functional"},{name:"Discretization, Pose Anchoring, and the Real-Time Solve",id:"discretization-and-solution"},{name:"Why No Material Properties, No Loads",id:"no-material-no-loads"},{name:"The Rivals: Ko Displacement Theory and Modal Methods",id:"rivals-comparison"},{name:"Practice: Weights, Sensor Economy, Element Accuracy",id:"practice-weights-sensors"},{name:"Applications and the 2023\u20132026 Frontier",id:"applications-frontier"}
        ] },
      { id: 'mod5', num: '5', title: "iFEM Elements & Formulations", file: 'mod5.html',
        sections: [
          {name:"From Functional to Elements: What an Inverse Element Is",id:"from-functional-to-elements"},{name:"Mindlin Kinematics and the Eight Section Strains",id:"mindlin-kinematics-section-strains"},{name:"Strain Rosettes: Membrane + Bending from Surface Data",id:"strain-rosettes-membrane-bending"},{name:"Interpolation and the Strain-Displacement Matrices B",id:"strain-displacement-matrices"},{name:"The Element Functional, k\u1d49 and f\u1d49",id:"element-functional"},{name:"The Inverse Timoshenko Beam Element",id:"inverse-timoshenko-beam"},{name:"iMIN3: The Three-Node Inverse Mindlin Plate Element",id:"imin3"},{name:"iQS4: The Four-Node Inverse Shell with Drilling DOF",id:"iqs4"},{name:"Assembly, Boundary Conditions, and the Real-Time Solve",id:"assembly-global-system"},{name:"RZT-iFEM: Zigzag Kinematics for Composites and Sandwich",id:"rzt-ifem"},{name:"The Element Zoo Today: Curved, Higher-Order, Hybrid",id:"element-zoo-recent"}
        ] },
      { id: 'mod6', num: '6', title: "Sensors, Placement & Deployment", file: 'mod6.html',
        sections: [
          {name:"From Strain to Shape: What the Hardware Must Deliver",id:"what-hardware-must-deliver"},{name:"Resistive Strain Gauges and Rosettes",id:"resistive-strain-gauges"},{name:"Fiber Optics: FBG Arrays and OFDR Distributed Sensing",id:"fiber-optic-sensing"},{name:"Sparse Coverage: Weighting for Missing Measurements",id:"sparse-weighting-formalism"},{name:"Sensor Count and Placement",id:"placement-optimization"},{name:"SEA Pre-Extrapolation: Manufacturing Virtual Sensors",id:"sea-pre-extrapolation"},{name:"Noise, Temperature, and Mounting",id:"noise-temperature-mounting"},{name:"A Deployment Recipe \u2014 and the Soft-Skin Outlook",id:"deployment-recipe-outlook"}
        ] },
    ]
  },
  {
    cluster: "The Wider Inverse-FEM Family",
    modules: [
      { id: 'mod7', num: '7', title: "Material Identification", file: 'mod7.html',
        sections: [
          {name:"Why Inverse Identification: From Standard Tests to Material Testing 2.0",id:"why-inverse-identification"},{name:"The Data: Full-Field Measurement by Digital Image Correlation",id:"full-field-measurement-dic"},{name:"Problem Statement and the Map of Identification Methods",id:"identification-problem-and-method-map"},{name:"FEMU: Finite Element Model Updating",id:"femu"},{name:"The Virtual Fields Method: Linear Case",id:"vfm-linear"},{name:"Nonlinear VFM and Sensitivity-Based Virtual Fields",id:"nonlinear-vfm"},{name:"Inverse Hyperelastic Characterization of Soft Materials",id:"hyperelastic-soft-materials"},{name:"Identifiability, Noise, and Test Design",id:"identifiability-noise-test-design"},{name:"FEMU vs VFM: An Honest Comparison",id:"femu-vs-vfm"},{name:"Beyond Parameters: Constitutive Model Discovery",id:"model-discovery"},{name:"A Practical Identification Workflow for a Silicone Skin",id:"practical-workflow"}
        ] },
      { id: 'mod8', num: '8', title: "Load & Contact Force Reconstruction", file: 'mod8.html',
        sections: [
          {name:"Every Elastic Body Is a Force Sensor",id:"elastic-body-as-force-sensor"},{name:"The Transfer Matrix: Condensing an FE Model into a Sensor Model",id:"transfer-matrix-formulation"},{name:"Why Naive Inversion Explodes: SVD Applied to $\\mathbf{H}$",id:"svd-ill-conditioning"},{name:"Tikhonov-Regularized Inversion",id:"tikhonov-regularization"},{name:"Choosing $\\lambda$: L-Curve, GCV, Discrepancy",id:"choosing-lambda"},{name:"Time-Domain Force Identification",id:"time-domain-force-identification"},{name:"From Structures to Skin: the Tactile Inverse Problem",id:"structures-to-skin"},{name:"Case Study: GelSlim 2.0 and Inverse FEM (Ma et al., ICRA 2019)",id:"case-study-gelslim-ifem"},{name:"Soft Robot Skins as Distributed Force Sensors: Design as Conditioning",id:"skin-design-as-conditioning"},{name:"Practical Recipe and Pitfalls",id:"practical-recipe-and-pitfalls"}
        ] },
      { id: 'mod9', num: '9', title: "Reference Configuration & Prestress", file: 'mod9.html',
        sections: [
          {name:"The Configuration You Never Measured",id:"reference-configuration-unknown"},{name:"Finite Kinematics, Just In Time",id:"finite-kinematics-refresher"},{name:"Four Configurations, Not Two",id:"four-configurations"},{name:"Shield Duality and the Eshelby Stress",id:"shield-duality-and-eshelby-stress"},{name:"Inverse Elastostatic Finite Elements",id:"inverse-elastostatic-finite-elements"},{name:"Fixed-Point Unloading: Relaxation, Acceleration, Continuation",id:"fixed-point-iteration-and-acceleration"},{name:"Prestressing Instead of Un-Deforming",id:"prestressing-mulf"},{name:"Uniqueness, Conditioning, and Static Determinacy",id:"uniqueness-conditioning-static-determinacy"},{name:"Practice: Choosing a Method, and the Pitfalls That Bite",id:"practice-and-pitfalls"},{name:"Applications and the 2023\u20132026 Frontier",id:"applications-and-frontier"}
        ] },
    ]
  },
  {
    cluster: "Modern Developments",
    modules: [
      { id: 'mod10', num: '10', title: "Adjoints & Differentiable FEM", file: 'mod10.html',
        sections: [
          {name:"From One-Shot Least Squares to Gradient-Based Inversion",id:"from-one-shot-to-gradients"},{name:"The Adjoint Method: One Extra Solve for the Whole Gradient",id:"adjoint-method"},{name:"Worked Example: Recovering a Stiffness Profile in a 1D Bar",id:"adjoint-worked-example"},{name:"Five Routes to the Same Gradient",id:"gradient-routes"},{name:"Differentiable FEM: Autodiff Meets the Stiffness Matrix",id:"differentiable-fem"},{name:"Dynamics, Contact, and the Quality of Gradients",id:"dynamics-contact-gradients"},{name:"Practical Recipes for a Soft Tactile Skin",id:"practical-recipes"}
        ] },
      { id: 'mod11', num: '11', title: "Learning-Enhanced Inversion", file: 'mod11.html',
        sections: [
          {name:"Why Learn Anything? Six Insertion Points",id:"insertion-points"},{name:"The Simplest Learned Map: Calibration Matrices, then Networks",id:"calibration-matrix"},{name:"Virtual Strains: GP Completion and Smuggled Priors",id:"sensor-completion"},{name:"FEM as a Training-Data Factory \u2014 and the Sim-to-Real Gap",id:"synthetic-training-data"},{name:"Per-Instance Physics: PINNs for Shape Sensing and Inverse Elasticity",id:"pinns"},{name:"When PINNs Fail \u2014 What a Low Loss Cannot Tell You",id:"pinn-failure-modes"},{name:"Amortized Inversion: Neural Operators",id:"neural-operators"},{name:"Structure and Hybrids: Shallow Decoders, GNNs, Residual Correction",id:"hybrids"},{name:"Head to Head: iFEM versus Learned Shape Sensing",id:"head-to-head"},{name:"Generalization, Leakage, and Out-of-Distribution Honesty",id:"generalization"},{name:"Case Study: the Tactile Skin, Learned-Map Angle",id:"tactile-case"},{name:"A Practitioner's Decision Procedure",id:"recipe"}
        ] },
      { id: 'mod12', num: '12', title: "Digital Twins & Frontiers", file: 'mod12.html',
        sections: [
          {name:"From Monitoring to Mirroring: What a Structural Digital Twin Is",id:"from-monitoring-to-mirroring"},{name:"The Engine Recap: iFEM in Five Equations",id:"ifem-recap-the-engine"},{name:"Real-Time by Construction",id:"real-time-by-construction"},{name:"The Payoff Is Stress: Recovery and Damage Indices",id:"stress-recovery-and-damage-indices"},{name:"Aerospace: Wing Shape Sensing and the Three-Method Shootout",id:"aerospace-wings"},{name:"Marine and Offshore: Hull Girders to Ship Twins",id:"marine-and-offshore"},{name:"Wind Energy: Shape Sensing a 61.5\u00a0m Composite Blade",id:"wind-energy-blades"},{name:"Composites and Stiffened Structures: When FSDT Isn't Enough",id:"composites-and-stiffened-structures"},{name:"Frontier: Soft Bodies, Tactile Skins, and Biomechanical Twins",id:"soft-bodies-tactile-and-biomech"},{name:"Open Problems, 2026 Edition",id:"open-problems-2026"},{name:"Practice: Build Your Own Lab-Scale Twin",id:"build-your-own-twin"}
        ] },
    ]
  },
];

// === SIDEBAR ===
function renderSidebar(activeModuleId) {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  let html = '<div class="sidebar-title"><span>iFEM — Inverse Finite Elements</span><button class="sidebar-toggle" onclick="toggleSidebar()" title="Hide sidebar">&times;</button></div>';

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
document.addEventListener('DOMContentLoaded', function() {
  initCollapsibles();
});
