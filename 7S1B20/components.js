// === MODULE DATA ===
const MODULES = [
  {
    cluster: 'Concepts',
    modules: [
      { id: 'cross-sections', num: '1', title: 'Inhomogeneous Cross-Sections', file: 'cross-sections.html',
        sections: [
          {name:'Hypotheses',id:'hypotheses'},
          {name:'Kinematics',id:'kinematics'},
          {name:'Constitutive Relations',id:'constitutive'},
          {name:'Stiffness Matrix',id:'stiffness-matrix'},
          {name:'Normal Force Center',id:'nc'},
          {name:'Stress: Pure Normal Force',id:'stress-normal'},
          {name:'Stress: Pure Bending',id:'stress-bending'},
          {name:'Shear: Single Material',id:'shear-single'},
          {name:'Shear: Multiple Materials',id:'shear-multi'}
        ] },
      { id: 'stress-state', num: '2', title: 'Stress State & Mohr\'s Circle', file: 'stress-state.html',
        sections: [
          {name:'3D Stress Tensor',id:'3d-tensor'},
          {name:'Cauchy\'s Formula',id:'cauchy'},
          {name:'Transformation (3D)',id:'transform-3d'},
          {name:'Transformation (2D)',id:'transform-2d'},
          {name:'Principal Stresses (3D)',id:'principal-3d'},
          {name:'Principal Stresses (2D)',id:'principal-2d'},
          {name:'Mohr\'s Circle',id:'mohr-construction'},
          {name:'Reading Mohr\'s Circle',id:'mohr-reading'},
          {name:'3D Mohr\'s Circle',id:'mohr-3d'}
        ] },
      { id: 'buckling', num: '3', title: 'Buckling & Instability', file: 'buckling.html',
        sections: [
          {name:'Classical vs Buckling',id:'classical-vs-buckling'},
          {name:'Ideal Column',id:'ideal-column'},
          {name:'Buckling Modes',id:'buckling-modes'},
          {name:'Effective Length',id:'effective-length'},
          {name:'Frame Buckling',id:'frame-buckling'},
          {name:'Slenderness',id:'slenderness'},
          {name:'Combined Loading',id:'combined-loading'},
          {name:'Design Criteria',id:'design-criteria'}
        ] },
      { id: 'plastic', num: '4', title: 'Plastic Analysis', file: 'plastic.html',
        sections: [
          {name:'Introduction',id:'intro'},
          {name:'Idealized Material',id:'material'},
          {name:'Rectangular Section',id:'rectangular'},
          {name:'General Section',id:'general-section'},
          {name:'M-N Interaction',id:'mn-interaction'},
          {name:'M-V Interaction',id:'mv-interaction'},
          {name:'Three Theorems',id:'three-theorems'},
          {name:'Static Method',id:'static-method'},
          {name:'Kinematic Method',id:'kinematic-method'},
          {name:'Frame Analysis',id:'frame-analysis'},
          {name:'Exam Exercises',id:'exam-exercises'}
        ] },
    ]
  },
  {
    cluster: 'Reference',
    modules: [
      { id: 'formulas', num: '∑', title: 'Formula Sheet', file: 'formulas.html',
        sections: [
          {name:'Stress Analysis 2D',id:'formulas-stress-2d'},
          {name:'Cross-Sections',id:'formulas-cross-sections'},
          {name:'Buckling',id:'formulas-buckling'},
          {name:'Plastic Analysis',id:'formulas-plastic'}
        ] },
    ]
  }
];

// === SIDEBAR ===
function renderSidebar(activeModuleId) {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  let html = '<div class="sidebar-title"><span>7S1B20 Applied Mechanics</span><button class="sidebar-toggle" onclick="toggleSidebar()" title="Hide sidebar">&times;</button></div>';

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
