'use strict';
const fs = require('node:fs');
const vm = require('node:vm');
const crypto = require('node:crypto');
const assert = require('node:assert/strict');
const path = require('node:path');
const out = '/tmp/modules-landscape-explorer-independent-evidence19-v1';
const spec = JSON.parse(fs.readFileSync(path.join(out,'dom-spec.json'),'utf8'));
const original = fs.readFileSync(path.join(out,'explorer-original.js'),'utf8');
const instrumented = fs.readFileSync(path.join(out,'explorer-instrumented.js'),'utf8');
const hash = value => crypto.createHash('sha256').update(value).digest('hex');
function boot(code) {
  const nodes = {};
  for (const [id, entry] of Object.entries(spec)) {
    nodes[id] = { ...entry.attributes, textContent:'', innerHTML:'', listeners:{},
      addEventListener(type,fn) {(this.listeners[type] ||= []).push(fn);},
      dispatch(type) {for (const fn of this.listeners[type] || []) fn();} };
  }
  const document = { getElementById(id) {
    assert.ok(nodes[id], 'unknown DOM id ' + id);
    return nodes[id];
  }};
  const context = vm.createContext({document});
  vm.runInContext(code, context, {filename:code === original ? 'explorer-original.js' : 'explorer-instrumented.js'});
  return {nodes,context};
}
const old = boot(original), current = boot(instrumented);
function domDigest(env) {
  return hash(JSON.stringify(Object.fromEntries(Object.entries(env.nodes).map(([id,n]) =>
    [id,{value:n.value,textContent:n.textContent,innerHTML:n.innerHTML}]))));
}
function compare() {assert.equal(domDigest(old),domDigest(current));}
function input(id,value) {
  for (const env of [old,current]) {env.nodes[id].value=String(value); env.nodes[id].dispatch('input');}
  compare();
}
function resample() {
  for (const env of [old,current]) env.nodes['ls-ce-resample'].dispatch('click');
  compare();
}
const cases = [];
function capture(name) {
  compare();
  const trace = JSON.parse(JSON.stringify(current.context.__ceTrace));
  trace.noiseSHA256 = hash(JSON.stringify(current.context.__ceAPI.noise()));
  trace.panelHTML = current.nodes['ls-ce-panel'].innerHTML;
  trace.svg1SHA256 = hash(current.nodes['ls-ce-svg1'].innerHTML);
  trace.svg2SHA256 = hash(current.nodes['ls-ce-svg2'].innerHTML);
  trace.originalAndInstrumentedDOMSHA256 = domDigest(current);
  const filename = path.join(out,name+'.json');
  fs.writeFileSync(filename,JSON.stringify(trace,null,2)+'\n',{flag:'wx'});
  const summary = {...trace};
  delete summary.Ns; delete summary.Zs; delete summary.trajs; delete summary.panelHTML;
  summary.name = name; summary.record = filename; summary.recordSHA256 = hash(fs.readFileSync(filename));
  summary.firstTrajectory = trace.trajs[0];
  cases.push(summary);
  return trace;
}
const defaultTrace = capture('default-seed1');
fs.writeFileSync(path.join(out,'common-noise-seed1.json'),JSON.stringify(current.context.__ceAPI.noise())+'\n',{flag:'wx'});
input('ls-ce-sig',0.1);
const exercise1 = capture('exercise-sigma01-seed1');
assert.equal(defaultTrace.noiseSHA256,exercise1.noiseSHA256);
input('ls-ce-T',5);
const short = capture('exercise-sigma01-T5-seed1');
for(let i=0;i<200;i++) assert.deepEqual(short.trajs[i],exercise1.trajs[i].slice(0,6));
assert.ok(short.violatingEpisodes <= exercise1.violatingEpisodes);
for(let i=0;i<200;i++) assert.ok(short.Ns[i] <= exercise1.Ns[i]);
input('ls-ce-T',40);
assert.equal(hash(JSON.stringify(current.context.__ceTrace.trajs)),hash(JSON.stringify(exercise1.trajs)));
resample();
const exercise2 = capture('exercise-sigma01-seed2');
assert.notEqual(exercise1.noiseSHA256,exercise2.noiseSHA256);
input('ls-ce-sig',0);
const zeroSafe = capture('zero-noise-k05-seed2');
assert.equal(zeroSafe.analyticEN,0); assert.equal(zeroSafe.violatingEpisodes,0);
input('ls-ce-k',1.25);
const equalSafe = capture('zero-noise-k125-boundary-equality-seed2');
assert.equal(equalSafe.trajs[0][1],1); assert.equal(equalSafe.analyticEN,0);
assert.equal(equalSafe.maxExcursion,0); assert.equal(equalSafe.violatingEpisodes,0);
input('ls-ce-k',1.5);
const overshoot = capture('zero-noise-k15-seed2');
assert.equal(overshoot.analyticEN,1); assert.equal(overshoot.violatingEpisodes,200);
input('ls-ce-k',1);
input('ls-ce-sig',0.01);
input('ls-ce-d',0);
const tiny = capture('tiny-noise-k1-sigma001-zero-budget-seed2');
assert.ok(tiny.analyticEN>0); assert.equal(tiny.zeroBudgetFails,true); assert.equal(tiny.cmdpPass,false);
assert.ok(tiny.panelHTML.includes('e-87'));
input('ls-ce-k',0.05);
const tinySlow = capture('tiny-noise-k005-sigma001-zero-budget-seed2');
assert.equal(tinySlow.zeroBudgetFails,true); assert.equal(tinySlow.cmdpPass,false);
assert.equal(current.context.__ceAPI.Q(96),0);
assert.ok(tinySlow.analyticEN>0);
input('ls-ce-k',0.5);
input('ls-ce-sig',0.07);
input('ls-ce-d',1);
resample();
capture('default-seed3');
const tailValues = [0,1,1.7320508075688772,6,8,8.2,8.3,9,20,38,39,96,-1,-9].map(z => {
  const directQ = current.context.__ceAPI.Q(z);
  return {z,directQ,subtractFromRoundedCDF:1-(1-directQ),format:current.context.__ceAPI.fp(directQ,3,true)};
});
// All batches keep the page's N=200, TMAX=100, seed generator and actual resample handler.
// Save every seed's count; the aggregate is empirical execution evidence, not a law theorem.
const large = boot(instrumented);
large.nodes['ls-ce-sig'].value='0.1'; large.nodes['ls-ce-sig'].dispatch('input');
const batches=[];
let totalViolations=0, totalCounts=0, totalCountSquares=0;
const batchCount=1000;
for(let batch=0;batch<batchCount;batch++) {
  if(batch)large.nodes['ls-ce-resample'].dispatch('click');
  const s=large.context.__ceTrace;
  const count=s.Ns.reduce((a,b)=>a+b,0);
  const sq=s.Ns.reduce((a,b)=>a+b*b,0);
  totalViolations+=s.violatingEpisodes; totalCounts+=count; totalCountSquares+=sq;
  batches.push({seedNo:s.seedNo,prngSeed:s.prngSeed,episodes:s.N,violatingEpisodes:s.violatingEpisodes,
    totalViolatingSteps:count,noiseSHA256:hash(JSON.stringify(large.context.__ceAPI.noise()))});
}
const n=batchCount*200, pv=totalViolations/n, mean=totalCounts/n;
const aggregate={settings:{k:0.5,sigma:0.1,T:40,goal:0.8,boundary:1},
  batchCount,episodes:n,seeds:{first:1,last:batchCount},totalViolations,totalCounts,
  jointEstimate:pv,nominalBernoulliSE:Math.sqrt(pv*(1-pv)/n),meanViolatingSteps:mean,
  nominalMeanCountSE:Math.sqrt((totalCountSquares-n*mean*mean)/(n-1)/n),batches};
fs.writeFileSync(path.join(out,'large-seed-batches.json'),JSON.stringify(aggregate,null,2)+'\n',{flag:'wx'});
const result={node:process.version,unchangedOriginalIIFEExecuted:true,
  strictFakeDOMUnknownIDCheck:true,originalVsInstrumentedAllScenarioDOMComparisonsPassed:true,
  commonNoiseReuseAndTrajectoryPrefixChecksPassed:true,cases,tailValues,
  aggregate:{...aggregate,batches:undefined},
  limitations:['No actual browser/rendering/layout test.','Finite deterministic PRNG and Box–Muller output have no formally certified iid exact Gaussian law.',
    'Execution numerics and nominal standard errors are not Lean proofs or confidence certificates.',
    'Direct Q avoids subtraction cancellation but can underflow outside double precision.']};
fs.writeFileSync(path.join(out,'harness-results.json'),JSON.stringify(result,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({cases:cases.map(c=>({name:c.name,analyticEN:c.analyticEN,jointEstimate:c.jointEstimate,
  sampleMeanCount:c.sampleMeanCount,noiseSHA256:c.noiseSHA256})),aggregate:result.aggregate,tailValues},null,2));
