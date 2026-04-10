// === MODULE DATA ===
const MODULES = [
  {
    cluster: 'Fairness',
    modules: [
      { id: 'part1', num: '1', title: 'Fairness: Concepts & Bias', file: 'part1.html',
        sections: [
          {name:'Five Dimensions',id:'dimensions'},{name:'Six Harms',id:'harms'},{name:'Four Data Biases',id:'biases'},{name:'Historical Bias Subtypes',id:'historical-subtypes'},{name:'Bias Pipeline',id:'bias-pipeline'},{name:'Bias-Harm Connections',id:'bias-harm-connections'},{name:'Key Case Studies',id:'case-studies'}
        ] },
      { id: 'part2', num: '2', title: 'Group Fairness Metrics', file: 'part2.html',
        sections: [
          {name:'Confusion Matrix',id:'confusion-matrix'},{name:'Performance Metrics',id:'performance-metrics'},{name:'Three Fairness Criteria',id:'fairness-criteria'},{name:'Incompatibility Theorem',id:'incompatibility'},{name:'Incompatibility Explorer',id:'incompatibility-explorer'},{name:'When to Use Which Metric',id:'when-to-use'},{name:'Challenges',id:'challenges'}
        ] },
      { id: 'part3', num: '3', title: 'Fairness-Aware ML Techniques', file: 'part3.html',
        sections: [
          {name:'No Fairness Through Unawareness',id:'unawareness'},{name:'Three Intervention Points',id:'interventions'},{name:'Pre-Processing',id:'pre-processing'},{name:'Reweighing Calculator',id:'reweighing-calculator'},{name:'Relabeling Step-Through',id:'relabeling-calculator'},{name:'In-Processing',id:'in-processing'},{name:'Post-Processing',id:'post-processing'},{name:'Reject Option Viz',id:'reject-option-viz'},{name:'Technique Comparison',id:'comparison'}
        ] },
      { id: 'part4', num: '4', title: 'Beyond Fairness-Aware ML', file: 'part4.html',
        sections: [
          {name:'EU Non-Discrimination Law',id:'eu-law'},{name:'Four-Fifths Rule',id:'four-fifths'},{name:'Five Abstraction Traps',id:'abstraction-traps'},{name:'Ethics Framework',id:'ethics'},{name:'Egalitarianism',id:'egalitarianism'}
        ] },
    ]
  },
  {
    cluster: 'Explainability',
    modules: [
      { id: 'part5', num: '5', title: 'XAI: Global Methods', file: 'part5.html',
        sections: [
          {name:'XAI Taxonomy',id:'taxonomy'},{name:'Motivations for XAI',id:'motivations'},{name:'Linear Regression',id:'linear-regression'},{name:'Logistic Regression',id:'logistic-regression'},{name:'Decision Trees',id:'decision-trees'},{name:'Global Surrogate',id:'global-surrogate'},{name:'Gini Importance',id:'gini'},{name:'PDP',id:'pdp'},{name:'ICE',id:'ice'},{name:'PDP vs ICE Explorer',id:'pdp-ice-explorer'}
        ] },
      { id: 'part6', num: '6', title: 'XAI: Local Methods', file: 'part6.html',
        sections: [
          {name:'LIME',id:'lime'},{name:'SHAP',id:'shap'},{name:'SHAP Waterfall Explorer',id:'shap-explorer'},{name:'LIME vs SHAP',id:'lime-vs-shap'},{name:'Counterfactual Explanations',id:'counterfactuals'},{name:'OOD Problem',id:'ood'}
        ] },
      { id: 'part7', num: '7', title: 'Evaluating Explanations', file: 'part7.html',
        sections: [
          {name:'Three Questions',id:'three-questions'},{name:'Properties of Good Explanations',id:'properties'},{name:'Truthfulness',id:'truthfulness'},{name:'Three Evaluation Levels',id:'evaluation-levels'},{name:'Key Findings',id:'findings'}
        ] },
    ]
  },
  {
    cluster: 'Privacy',
    modules: [
      { id: 'part8', num: '8', title: 'Privacy & Differential Privacy', file: 'part8.html',
        sections: [
          {name:'Privacy Attacks',id:'attacks'},{name:'k-Anonymity',id:'k-anonymity'},{name:'Differential Privacy',id:'dp-definition'},{name:'Privacy Budget',id:'epsilon'},{name:'Sensitivity',id:'sensitivity'},{name:'Laplace Mechanism',id:'laplace'},{name:'Key Properties',id:'dp-properties'},{name:'Laplace Explorer',id:'laplace-explorer'}
        ] },
      { id: 'part9', num: '9', title: 'Federated Learning', file: 'part9.html',
        sections: [
          {name:'Definition',id:'definition'},{name:'FedAvg Algorithm',id:'fedavg'},{name:'Global Loss',id:'global-loss'},{name:'Challenges',id:'challenges'},{name:'DP in FL',id:'dp-in-fl'},{name:'Secure Aggregation',id:'secure-aggregation'},{name:'Three-Way Trade-off',id:'tradeoff'}
        ] },
    ]
  },
  {
    cluster: 'Critical Thinking',
    modules: [
      { id: 'part10', num: '10', title: 'Calling Bullshit', file: 'part10.html',
        sections: [
          {name:'Four Questions',id:'four-questions'},{name:'Misleading Info Taxonomy',id:'taxonomy'},{name:'Correlation vs Causation',id:'correlation'},{name:'Visualization Tricks',id:'visualization'},{name:'AI & Disinformation',id:'ai-disinfo'},{name:'Brandolini\'s Law',id:'brandolini'}
        ] },
    ]
  }
];

// === SIDEBAR ===
function renderSidebar(activeModuleId) {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  let html = '<div class="sidebar-title"><span>2IX30 Responsible DS</span><button class="sidebar-toggle" onclick="toggleSidebar()" title="Hide sidebar">&times;</button></div>';

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
