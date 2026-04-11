// === MODULE DATA ===
const MODULES = [
  {
    cluster: 'Classical CV',
    modules: [
      { id: 'mod1', num: '1', title: 'Feature Extraction & Matching', file: 'mod1.html',
        sections: [
          {name:'Color Systems',id:'color-systems'},{name:'Features Overview',id:'features-overview'},{name:'Canny Edge Detection',id:'canny-edge-detection'},{name:'HOG Descriptor',id:'hog-descriptor'},{name:'SIFT',id:'sift'},{name:'Feature Matching',id:'feature-matching'},{name:'Hough Transform',id:'hough-transform'},{name:'Harris Corner Detector',id:'harris-corner-detector'},{name:'Haar-like Features',id:'haar-features'}
        ] },
      { id: 'mod2', num: '2', title: 'Classification — Clustering', file: 'mod2.html',
        sections: [
          {name:'Classification vs Detection',id:'classification-vs-detection'},{name:'Supervised vs Unsupervised',id:'ml-types'},{name:'K-Means Clustering',id:'kmeans-intuition'},{name:'K-Means Mathematics',id:'kmeans-math'},{name:'K-Means on Digits',id:'kmeans-digits'},{name:'K-Means Properties',id:'kmeans-properties'},{name:'Gaussian Mixture Models',id:'gmm-motivation'},{name:'Gaussian Distributions',id:'gaussian-basics'},{name:'EM Algorithm',id:'em-algorithm'},{name:'GMM Summary',id:'gmm-summary'},{name:'PCA',id:'pca'}
        ] },
      { id: 'mod3', num: '3', title: 'Classification — Supervised', file: 'mod3.html',
        sections: [
          {name:'Supervised Classification',id:'supervised-intro'},{name:'Semantic Gap',id:'semantic-gap'},{name:'Nearest Neighbour',id:'nearest-neighbour'},{name:'K-NN',id:'knn'},{name:'Linear Classifiers',id:'linear-classifiers'},{name:'Haar-like Features',id:'haar-features'},{name:'Dataset Splitting',id:'dataset-splitting'},{name:'SVC (Linear)',id:'svc'},{name:'SVM Kernels',id:'svm-kernels'},{name:'AdaBoost',id:'adaboost'},{name:'Object Detection',id:'object-detection'}
        ] },
    ]
  },
  {
    cluster: 'Deep Learning',
    modules: [
      { id: 'mod4', num: '4', title: 'DL Fundamentals', file: 'mod4.html',
        sections: [
          {name:'Why Deep Learning',id:'motivation'},{name:'The Neuron',id:'neuron'},{name:'Network Architecture',id:'architecture'},{name:'Activation Functions',id:'activation-functions'},{name:'Forward Propagation',id:'forward-propagation'},{name:'SoftMax',id:'softmax'},{name:'Loss Functions',id:'loss-functions'},{name:'Gradient Descent',id:'gradient-descent'},{name:'Backpropagation',id:'backpropagation'},{name:'Training Pipeline',id:'training-pipeline'},{name:'Overfitting',id:'overfitting'},{name:'Hierarchical Learning',id:'hierarchical-learning'}
        ] },
      { id: 'mod5', num: '5', title: 'Classification with Deep Learning', file: 'mod5.html',
        sections: [
          {name:'FCN Limitations',id:'fcn-limitations'},{name:'CNN Innovations',id:'cnn-innovations'},{name:'Convolution',id:'convolution'},{name:'3D Convolutions',id:'3d-convolution'},{name:'Pooling',id:'pooling'},{name:'CNN Pipeline',id:'cnn-pipeline'},{name:'1x1 Convolution',id:'1x1-conv'},{name:'Stride and Padding',id:'stride-padding'},{name:'Regularization',id:'overfitting-reg'},{name:'Dropout',id:'dropout'},{name:'Batch Normalization',id:'batch-norm'},{name:'Weight Initialization',id:'weight-init'},{name:'Optimizers',id:'optimizers'},{name:'Feature Visualization',id:'feature-viz'},{name:'Metrics',id:'metrics'}
        ] },
      { id: 'mod5-1', num: '5.1', title: 'CNN Architecture Landscape', file: 'mod5-1.html',
        sections: [
          {name:'ImageNet',id:'imagenet'},{name:'AlexNet',id:'alexnet'},{name:'ZFNet',id:'zfnet'},{name:'VGGNet',id:'vggnet'},{name:'GoogLeNet',id:'googlenet'},{name:'ResNet',id:'resnet'},{name:'ResNet Variants',id:'variants'},{name:'DenseNet',id:'densenet'},{name:'NASNet',id:'nasnet'},{name:'Other Architectures',id:'other'},{name:'Summary',id:'summary'}
        ] },
      { id: 'mod6', num: '6', title: 'Object Detection', file: 'mod6.html',
        sections: [
          {name:'Problem Definition',id:'problem'},{name:'Applications',id:'applications'},{name:'Challenges',id:'challenges'},{name:'BBox Regression',id:'bbox-regression'},{name:'Two-Stage Detectors',id:'two-stage'},{name:'Single-Stage Detectors',id:'single-stage'},{name:'Anchor Boxes',id:'anchors'},{name:'FPN',id:'fpn'},{name:'RetinaNet',id:'retinanet'},{name:'NMS',id:'nms'},{name:'Evaluation',id:'evaluation'},{name:'Comparison',id:'comparison'}
        ] },
    ]
  },
  {
    cluster: '3D Geometry & Sensing',
    modules: [
      { id: 'mod7', num: '7', title: 'Camera Model', file: 'mod7.html',
        sections: [
          {name:'Pinhole Model',id:'pinhole'},{name:'Projective Geometry',id:'projective-geometry'},{name:'Vanishing Points',id:'vanishing-points'},{name:'Homogeneous Coordinates',id:'homogeneous'},{name:'Projection Matrix',id:'projection-matrix'},{name:'Intrinsic Parameters',id:'intrinsic'},{name:'Extrinsic Parameters',id:'extrinsic'},{name:'Full Camera Matrix',id:'full-matrix'},{name:'Calibration',id:'calibration'},{name:'Homography',id:'homography'}
        ] },
      { id: 'mod8', num: '8', title: '3D Sensors & Depth Sensing', file: 'mod8.html',
        sections: [
          {name:'Sensor Taxonomy',id:'taxonomy'},{name:'Stereo Vision',id:'stereo'},{name:'Time-of-Flight',id:'tof'},{name:'Structured Light',id:'structured-light'},{name:'Passive vs Active',id:'passive-vs-active'},{name:'LiDAR',id:'lidar'},{name:'4D Radar',id:'radar'},{name:'Sonar',id:'sonar'},{name:'Sensor Comparison',id:'sensor-comparison'},{name:'3D Data Formats',id:'3d-formats'}
        ] },
    ]
  },
  {
    cluster: '3D Reconstruction',
    modules: [
      { id: 'mod9a', num: '9A', title: 'NeRF', file: 'mod9a.html',
        sections: [
          {name:'3D Formats',id:'3d-formats'},{name:'Rendering vs Inverse',id:'rendering-vs-inverse'},{name:'Camera Poses',id:'camera-poses'},{name:'Volume Rendering (Continuous)',id:'volume-rendering-continuous'},{name:'Volume Rendering (Discrete)',id:'volume-rendering-discrete'},{name:'NeRF Architecture',id:'nerf-architecture'},{name:'Positional Encoding',id:'positional-encoding'},{name:'Hierarchical Sampling',id:'hierarchical-sampling'},{name:'Training and Loss',id:'training-loss'},{name:'Variants',id:'limitations-variants'}
        ] },
      { id: 'mod9b', num: '9B', title: '3D Gaussian Splatting', file: 'mod9b.html',
        sections: [
          {name:'Motivation',id:'motivation'},{name:'Gaussian Fundamentals',id:'gaussian-fundamentals'},{name:'Gaussian Primitives',id:'gaussian-primitive'},{name:'Pipeline Overview',id:'pipeline-overview'},{name:'SfM Initialization',id:'sfm-initialization'},{name:'Projection',id:'projection'},{name:'Rasterization',id:'rasterization'},{name:'Spherical Harmonics',id:'spherical-harmonics'},{name:'Covariance Decomposition',id:'covariance-decomposition'},{name:'Loss Function',id:'loss-function'},{name:'Adaptive Density',id:'adaptive-density'},{name:'NeRF vs 3DGS',id:'nerf-vs-3dgs'},{name:'Future Directions',id:'future-directions'}
        ] },
      { id: 'mod10-slam', num: '10', title: 'SLAM', file: 'mod10-slam.html',
        sections: [
          {name:'3D Challenges',id:'3d-challenges'},{name:'SLAM Intro',id:'slam-intro'},{name:'SLAM Types',id:'slam-types'},{name:'SLAM Pipeline',id:'slam-pipeline'},{name:'Drift and Loop Closure',id:'drift-loop-closure'},{name:'KinectFusion',id:'kinectfusion'},{name:'TSDF',id:'tsdf'},{name:'Back-Projection',id:'back-projection'},{name:'ICP',id:'icp'},{name:'Pose Transform',id:'pose-transform'},{name:'RANSAC',id:'ransac-icp'},{name:'TSDF Update',id:'tsdf-update'},{name:'Ray-Casting',id:'raycasting'},{name:'Marching Cubes',id:'marching-cubes'}
        ] },
    ]
  },
  {
    cluster: '3D Processing & Analysis',
    modules: [
      { id: 'mod10-ae', num: '10', title: 'Autoencoders', file: 'mod10-ae.html',
        sections: [
          {name:'Anomaly Detection',id:'anomaly-detection'},{name:'Outlier Detection',id:'outlier-detection'},{name:'Autoencoder Concept',id:'autoencoder-concept'},{name:'Architecture',id:'architecture'},{name:'Anomaly Score',id:'anomaly-score'},{name:'Denoising AE',id:'denoising-ae'},{name:'Convolutional AE',id:'convolutional-ae'},{name:'Pooling/Unpooling',id:'pooling-unpooling'},{name:'Hyperparameters',id:'hyperparameters'},{name:'Loss Functions',id:'loss-functions'},{name:'VAE',id:'vae'}
        ] },
      { id: 'mod11', num: '11', title: '3D Data Fusion', file: 'mod11.html',
        sections: [
          {name:'Motivation',id:'motivation'},{name:'Data Types',id:'data-types'},{name:'LiDAR vs RGB-D',id:'sensor-comparison'},{name:'Fusion Pipeline',id:'fusion-pipeline'},{name:'Stage 1: Data Format',id:'stage1'},{name:'Stage 2: Coordinates',id:'stage2'},{name:'Stage 3: Fusion',id:'stage3'},{name:'KinectFusion Limits',id:'kinectfusion-limits'},{name:'Rolling Buffer',id:'rolling-buffer'},{name:'Drift',id:'drift'},{name:'Chained TSDF',id:'chained-tsdf'},{name:'Plane Correction',id:'plane-correction'},{name:'SVD Pose Estimation',id:'svd'}
        ] },
      { id: 'mod12', num: '12', title: '3D Data Analysis', file: 'mod12.html',
        sections: [
          {name:'Challenges',id:'challenges'},{name:'Three Families',id:'three-families'},{name:'MVCNN',id:'mvcnn'},{name:'SnapNet',id:'snapnet'},{name:'VoxNet and 3D CNNs',id:'voxnet'},{name:'PointNet Intro',id:'pointnet-intro'},{name:'PointNet Architecture',id:'pointnet-arch'},{name:'Advanced Architectures',id:'advanced'},{name:'Comparison',id:'comparison'}
        ] },
    ]
  },
  {
    cluster: 'Video & Behaviour',
    modules: [
      { id: 'mod13', num: '13', title: 'Behaviour Analysis', file: 'mod13.html',
        sections: [
          {name:'Problem Definition',id:'definition'},{name:'Action Recognition',id:'action-recognition'},{name:'Two-Stream',id:'two-stream'},{name:'2D vs 3D Convolutions',id:'conv3d'},{name:'CNN + LSTM',id:'lstm-pipeline'},{name:'Anomaly (Outlier)',id:'anomaly-outlier'},{name:'Autoencoders',id:'autoencoders'},{name:'Convolutional AE',id:'cae'},{name:'I3D',id:'i3d'},{name:'MIL',id:'mil'},{name:'SlowFast',id:'slowfast'},{name:'Crowd Analysis',id:'crowd'}
        ] },
    ]
  }
];

// === SIDEBAR ===
function renderSidebar(activeModuleId) {
  const sidebar = document.getElementById('sidebar');
  if (!sidebar) return;

  let html = '<div class="sidebar-title"><span>5LSH0 Computer Vision</span><button class="sidebar-toggle" onclick="toggleSidebar()" title="Hide sidebar">&times;</button></div>';

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
