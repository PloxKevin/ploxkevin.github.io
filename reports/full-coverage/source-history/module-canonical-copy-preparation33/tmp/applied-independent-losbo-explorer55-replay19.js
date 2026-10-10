const fs = require('fs');
const vm = require('vm');
const crypto = require('crypto');
const defaults={norm:'10',beta:'2',bfac:'1',lfac:'1',efac:'2',beps:'0.05',K:'40',show:'1',noise:'uniform',model:'losbo'};
const elements=new Map();
function getElementById(id){
  if(!elements.has(id)){
    const el={id,value:defaults[id.replace('st-mc-','')]??'',textContent:'',innerHTML:'',max:'',events:{},addEventListener(kind,cb){(this.events[kind]??=[]).push(cb);},dispatch(kind){for(const cb of this.events[kind]??[])cb({target:this});}};
    elements.set(id,el);
  }
  return elements.get(id);
}
const context={document:{getElementById},Math,console};
context.globalThis=context;
vm.createContext(context);
const file='/tmp/modules-losbo-gaussian-explorer19-instrumented.js';
vm.runInContext(fs.readFileSync(file,'utf8'),context,{filename:file,timeout:120000});
const defaultSummary=context.__readonlyTheoryMonteCarlo.summarize();
getElementById('st-mc-noise').value='gauss';
getElementById('st-mc-noise').dispatch('change');
const runs=[];
for(let batch=0;batch<20;batch++){
  if(batch>0)getElementById('st-mc-resample').dispatch('click');
  const snap=context.__readonlyTheoryMonteCarlo.snapshot();
  const stats=context.__readonlyTheoryMonteCarlo.summarize();
  const counted={};
  for(const alg of ['safeopt','realbeta','losbo']){
    let unsafe=0,absExceed=0,positiveExceed=0,negativeExceed=0,total=0;
    for(let f=0;f<snap.results[alg].length;f++){
      const F=snap.results.funcs[f];
      for(const q of snap.results[alg][f].queries){
        const idx=Math.round(q.x*(snap.N-1));
        if(q.x!==snap.grid[idx])throw new Error('Exact grid identity failed');
        const truth=F.fv[idx],eps=q.y-truth;
        if(q.bad!==(truth<F.h))throw new Error('Actual unsafe flag mismatch');
        if(q.bad)unsafe++;
        if(Math.abs(eps)>0.1)absExceed++;
        if(eps>0.1)positiveExceed++;
        if(eps< -0.1)negativeExceed++;
        total++;
      }
    }
    counted[alg]={totalQueries:total,unsafeQueries:unsafe,absoluteNoiseExceedances:absExceed,positiveNoiseExceedances:positiveExceed,negativeNoiseExceedances:negativeExceed,unsafeQueryFraction:unsafe/total,absoluteExceedanceFraction:absExceed/total};
    if(total!==snap.results.funcs.length*snap.T||stats[alg].per!==unsafe/snap.results.funcs.length)throw new Error('Stats/count mismatch');
  }
  runs.push({seed:snap.seed,settings:Object.fromEntries(Object.entries(defaults).map(([k,v])=>[k,getElementById('st-mc-'+k).value])),constants:{N:snap.N,M:snap.M,T:snap.T,ELL:snap.ELL,DELTA:snap.DELTA},stats,counted,results:snap.results,renderedTable:getElementById('st-mc-table').innerHTML,renderedNote:getElementById('st-mc-note').innerHTML});
}
const total=Object.fromEntries(['safeopt','realbeta','losbo'].map(alg=>[alg,{totalQueries:0,unsafeQueries:0,absoluteNoiseExceedances:0,positiveNoiseExceedances:0,negativeNoiseExceedances:0}]));
for(const run of runs)for(const alg of Object.keys(total))for(const k of Object.keys(total[alg]))total[alg][k]+=run.counted[alg][k];
const output={status:'actual_headless_simulation_observation',nodeVersion:process.version,source:'/home/oxrexkevin/SafetyBased/SafeLearning/safe-bo-theory.html',sourceSha256:crypto.createHash('sha256').update(fs.readFileSync('/home/oxrexkevin/SafetyBased/SafeLearning/safe-bo-theory.html')).digest('hex'),instrumentedFile:file,instrumentedSha256:crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex'),defaultUniformSummary:defaultSummary,gaussianBatches:runs,total,limits:['Actual source code executed via Node/fake DOM with original event handlers; no browser, viewport or human/physical observation.','Finite reproducible seeds11..20/settings only, seeded PRNG and floating-point GP; observed unsafe frequencies are not universal probabilistic safety guarantees.','All original book/proof/compiler/review files remain unchanged; evidence is TMP-only during HOLD33.']};
const out='/tmp/applied-independent-losbo-explorer55-replay19-result.json';
if(fs.existsSync(out))throw new Error('Output already exists');
fs.writeFileSync(out,JSON.stringify(output,null,2)+'\n');
console.log(JSON.stringify({output:out,sha256:crypto.createHash('sha256').update(fs.readFileSync(out)).digest('hex'),total,seeds:runs.map(r=>r.seed)},null,2));
