'use strict';
const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const out='/tmp/modules-landscape-explorer-independent-evidence19-v1';
const spec=JSON.parse(fs.readFileSync(out+'/dom-spec.json','utf8'));
function boot(file){
  const nodes={};
  for(const [id,s] of Object.entries(spec))nodes[id]={...s.attributes,textContent:'',innerHTML:'',listeners:{},
    addEventListener(type,f){(this.listeners[type]||=[]).push(f);},
    dispatch(type){for(const f of this.listeners[type]||[])f();}};
  const context=vm.createContext({document:{getElementById(id){assert.ok(nodes[id]);return nodes[id];}}});
  vm.runInContext(fs.readFileSync(out+'/'+file,'utf8'),context,{filename:file});
  return {nodes,context};
}
const a=boot('explorer-original.js'),b=boot('explorer-instrumented.js');
const digest=e=>crypto.createHash('sha256').update(JSON.stringify(Object.fromEntries(Object.entries(e.nodes).map(([id,n])=>
  [id,{value:n.value,textContent:n.textContent,innerHTML:n.innerHTML}])))).digest('hex');
for(const [id,val] of [['ls-ce-k','0.05'],['ls-ce-sig','0.01'],['ls-ce-T','5'],['ls-ce-d','0']]){
  for(const env of [a,b]){env.nodes[id].value=val;env.nodes[id].dispatch('input');}
  assert.equal(digest(a),digest(b));
}
const trace=JSON.parse(JSON.stringify(b.context.__ceTrace));
assert.equal(trace.analyticEN,0);
assert.equal(trace.zeroBudgetFails,true);assert.equal(trace.cmdpPass,false);
assert.ok(b.nodes['ls-ce-panel'].innerHTML.includes('positive, below the double-precision range'));
const terms=[];
for(let t=1;t<=5;t++){
  const m=.8*(1-Math.pow(.95,t)),v=.0001*(1-Math.pow(.95,2*t))/(1-.95*.95);
  const z=(1-m)/Math.sqrt(v);
  terms.push({t,m,v,z,implementedQ:b.context.__ceAPI.Q(z)});
  assert.ok(v>0);assert.equal(terms.at(-1).implementedQ,0);
}
const record={node:process.version,settingsWithinActualSliderLimits:true,
  originalAndInstrumentedDOMSHA256:digest(b),terms,trace,panelHTML:b.nodes['ls-ce-panel'].innerHTML,
  conclusion:'All five actual binary64 marginal tails and their sum underflow to 0, while positive sigma implies positive true tails. The existing explicit zero-budget guard correctly fails and the display reports positivity below double precision.',
  noBrowserOrFormalNumericProof:true};
fs.writeFileSync(out+'/allowed-slider-complete-tail-underflow.json',JSON.stringify(record,null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({terms,analyticEN:trace.analyticEN,zeroBudgetFails:trace.zeroBudgetFails,cmdpPass:trace.cmdpPass}));
