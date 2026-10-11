const fs=require('node:fs'),vm=require('node:vm'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const sha=b=>crypto.createHash('sha256').update(b).digest('hex');
const sourcePath='/home/oxrexkevin/SafetyBased/SafeLearning/gosafe.html';
const html=fs.readFileSync(sourcePath,'utf8');
const marker='// ===== Explorer: local vs global safe exploration =====';
const start=html.indexOf('    (function () {',html.indexOf(marker));
const end=html.indexOf('    })();',start)+'    })();'.length;
assert(start>0 && end>start);
const original=html.slice(start,end);
const hook=`
      globalThis.__explorerAudit={
        reset:reset,experiment:experiment,rollout:rollout,pickMax:pickMax,kern:kern,boundary:boundary,
        state:function(){return {settings:{N:N,P:P,DT:DT,K:K,W:W,X0:X0,ELL:ELL,SN:SN,EPS:EPS,NMAX:NMAX,NGE:NGE,BSTRIDE:BSTRIDE,TIE:TIE},
          ctrl:Object.assign({},ctrl),grid:grid.map(function(a){return Object.assign({},a)}),
          gTrue:Array.from(gTrue),fTrue:Array.from(fTrue),dist:Array.from(dist),LA_TRUE:LA_TRUE,XI_TRUE:XI_TRUE,
          SEED_P:SEED_P,OPT_P:OPT_P,fOpt:fOpt,Xd:Xd.slice(),yf:yf.slice(),yg:yg.slice(),
          lf:Array.from(lf),uf:Array.from(uf),lg:Array.from(lg),ug:Array.from(ug),S:Array.from(S),E:Array.from(E),
          B:B.map(function(a){return Object.assign({},a)}),n:n,phase:phase,lseCount:lseCount,geCount:geCount,nLSE:nLSE,
          done:done,violations:violations,backups:backups,evals:evals.map(function(a){return Object.assign({},a)}),
          lastRoll:lastRoll,logLines:logLines.slice(),converged:converged}}
      };
`;
const instrumented=original.slice(0,original.lastIndexOf('    })();'))+hook+'    })();';
assert.equal(instrumented.replace(hook,''),original);
const extractedPath='/tmp/modules-gosafe-explorer19-applied-rerun-exact-iife.js';
const instrumentedPath='/tmp/modules-gosafe-explorer19-applied-rerun-instrumented-iife.js';
fs.writeFileSync(extractedPath,original);fs.writeFileSync(instrumentedPath,instrumented);
const nodes=new Map();
const defaults={'gs-mode':'gosafeopt','gs-beta':'3','gs-la':'9','gs-lx':'1','gs-xi':'1'};
function node(id){if(!nodes.has(id))nodes.set(id,{id,value:defaults[id]||'',checked:id==='gs-bc',textContent:'',innerHTML:'',listeners:{},addEventListener(kind,fn){this.listeners[kind]=fn;}});return nodes.get(id);}
const context={document:{getElementById:node},setTimeout(){throw new Error('Timer callback unexpectedly invoked')},clearTimeout(){}};
vm.runInNewContext(instrumented,context,{filename:instrumentedPath,timeout:30000});
const audit=context.__explorerAudit;
const close=(x,y,t=1e-11)=>assert(Math.abs(x-y)<=t,`${x} differs from ${y}`);
let initial=audit.state();
assert.deepEqual(JSON.parse(JSON.stringify(initial.settings)),{N:25,P:625,DT:.0025,K:1200,W:.6,X0:0,ELL:.12,SN:.02,EPS:.2,NMAX:160,NGE:6,BSTRIDE:30,TIE:.001});
assert.equal(initial.Xd.length,1);assert.equal(initial.Xd[0],initial.SEED_P);assert.equal(initial.B.length,43);
assert.equal(initial.lastRoll.xs.length,1201);assert.equal(initial.B[41].x,initial.lastRoll.xs[1200]);assert.equal(initial.B[42].x,initial.lastRoll.xs[1200]);
for(let k=1;k<=41;k++)assert.equal(initial.B[k].x,initial.lastRoll.xs[(k-1)*30]);
let safe=0,first=0,second=0,worstClosedFormError=0,worstPrefixGap=0,violatingRollouts=0;
for(let p=0;p<625;p++){
 const a=initial.grid[p],gain=3+5*a.a2,reference=.8*(1+Math.cos(4*Math.PI*a.a1)),eq=(gain*reference+.6)/(1+gain),ratio=1-.0025*(1+gain);
 close(initial.gTrue[p],1-eq);
 const roll=audit.rollout(p,false);assert.equal(roll.xs.length,1201);assert.equal(roll.trig,-1);
 let min=Infinity;
 for(let k=0;k<=1200;k++){
   const exact=eq+Math.pow(ratio,k)*(0-eq);
   worstClosedFormError=Math.max(worstClosedFormError,Math.abs(exact-roll.xs[k]));
   min=Math.min(min,1-Math.abs(roll.xs[k]));
 }
 const gap=min-initial.gTrue[p];assert(gap>=-1e-12 && gap<1e-5);worstPrefixGap=Math.max(worstPrefixGap,gap);
 if(roll.viol)violatingRollouts++;
 if(initial.gTrue[p]>=0){safe++;a.a1<.5?first++:second++;}
}
assert.equal(safe,350);assert.equal(first,175);assert.equal(second,175);assert(worstClosedFormError<1e-12);
close(initial.LA_TRUE,128/15,1e-6);close(initial.XI_TRUE,.0605);close(initial.settings.K*initial.settings.DT,3);
let independentLA=0,attainer=null;
for(let p=0;p<625;p++)for(let q=p+1;q<625;q++){
 const d=Math.hypot(initial.grid[p].a1-initial.grid[q].a1,initial.grid[p].a2-initial.grid[q].a2);
 const slope=Math.abs(initial.gTrue[p]-initial.gTrue[q])/d;
 if(slope>independentLA){independentLA=slope;attainer=[p,q];}
}
close(independentLA,128/15,1e-12);
const seed=initial.SEED_P,A=1+.02*.02+1e-8;
let worstSeedPosteriorDeviation=0;
for(let p=0;p<625;p++){
 const k=audit.kern(p,seed),sd=Math.sqrt(Math.max(1-k*k/A,0));
 const mf=k*initial.yf[0]/A,mg=k*initial.yg[0]/A;
 for(const [actual,expected] of [[initial.lf[p],mf-3*sd],[initial.uf[p],mf+3*sd],[initial.lg[p],p===seed?Math.max(0,mg-3*sd):mg-3*sd],[initial.ug[p],mg+3*sd]]){
   worstSeedPosteriorDeviation=Math.max(worstSeedPosteriorDeviation,Math.abs(actual-expected));close(actual,expected,2e-12);
 }
}
audit.reset();const seeded1=audit.state();
audit.reset();const seeded2=audit.state();
assert.deepEqual(Array.from(seeded1.yf),Array.from(seeded2.yf));assert.deepEqual(Array.from(seeded1.yg),Array.from(seeded2.yg));
const score=p=>p===0?1:p===1?.9995:p===2?.998:null;
const pick1=audit.pickMax(score);assert([0,1].includes(pick1));
audit.reset();const pick2=audit.pickMax(score);assert.equal(pick1,pick2);
function run(mode,steps){
 node('gs-mode').value=mode;audit.reset();let previous=audit.state(),trace=[];
 for(let i=0;i<steps && !previous.done;i++){
  audit.experiment();const next=audit.state();
  assert(next.n<=160);assert(next.lastRoll.xs.length===1201);
  for(let p=0;p<625;p++){
   assert(next.S[p]>=previous.S[p]);assert(next.lg[p]>=previous.lg[p]);assert(next.lf[p]>=previous.lf[p]);
   assert(next.ug[p]<=previous.ug[p]);assert(next.uf[p]<=previous.uf[p]);
  }
  if(next.evals.length>previous.evals.length){
   const event=next.evals[next.evals.length-1];
   if(event.kind==='lse' || event.kind==='geok'){
    assert.equal(next.Xd.length,previous.Xd.length+1);assert.equal(next.B.length,previous.B.length+42);
   }else if(event.kind==='gefail'){
    assert.equal(next.Xd.length,previous.Xd.length);assert.equal(next.B.length,previous.B.length);assert(next.lastRoll.trig>=0);
   }else assert.fail('Unknown actual event');
  }
  trace.push({n:next.n,phase:next.phase,kind:next.evals[next.evals.length-1].kind,parameter:next.lastRoll.p,trigger:next.lastRoll.trig,backup:next.lastRoll.pb,observations:next.Xd.length,backups:next.B.length,safeCount:next.S.reduce((a,b)=>a+b,0),excludedCount:next.E.reduce((a,b)=>a+b,0),violations:next.violations,done:next.done});
  previous=next;
 }
 return {mode,trace,final:{n:previous.n,done:previous.done,violations:previous.violations,converged:previous.converged},logs:previous.logLines};
}
const safeopt=run('safeopt',24),gosafeopt=run('gosafeopt',32);
assert.equal(node('gs-la-val').textContent.split('(true ')[1],'8.5)');
const report={status:'passed_read_only_actual_explorer_execution',source:sourcePath,source_sha256:sha(Buffer.from(html)),exact_explorer_iife:extractedPath,exact_explorer_iife_sha256:sha(Buffer.from(original)),instrumented_explorer_iife:instrumentedPath,instrumented_explorer_iife_sha256:sha(Buffer.from(instrumented)),instrumentation:'One closure export inserted immediately before the original final IIFE close; every original implementation byte retained. DOM objects store controls/text/events; no browser or rendering assertions.',node_version:process.version,settings:initial.settings,all_625_actual_uninterrupted_rollouts:{steps_per_rollout:1200,samples:1201,worst_closed_form_deviation:worstClosedFormError,worst_prefix_infimum_gap:worstPrefixGap,violating_rollouts:violatingRollouts,safe_parameters:safe,first_island:first,second_island:second},finite_grid_constants:{implementation_LA_float32_distance:initial.LA_TRUE,independent_float64_hypot_LA:independentLA,attainer,mathematical_candidate:128/15,implementation_XI:initial.XI_TRUE},gp_initial_actual_separate_columns:{observations:1,effective_kernel_diagonal:A,declared_noise_standard_deviation:.02,additional_jitter:1e-8,cholesky_pivot_floor:1e-12,max_closed_form_posterior_deviation:worstSeedPosteriorDeviation},seeded_tie_test:{accepted_scores:[1,.9995],excluded_score:.998,repeatable_selected_index:pick1,tolerance:.001},safeopt,gosafeopt,literal_limits:['Actual headless NodeVM execution with fakeDOM; no browser launch/viewport/network/live-site pass.','Floating point numerical evidence is separate from Lean mathematical proof and does not prove a universal exact maximum.','Separate f/g posterior columns and seeded Gaussian draws substantiate described implementation structure, not a stochastic independence theorem about pseudorandom outputs.','Actual GP factorization includes1e-8 jitter and a1e-12 pivot floor, so literal exactK+sigma²I wording needs qualification.','Actual next-slider trueLa text displays8.5 (one decimal), while resetlog displays8.53 (two decimals).','Finite fixed-control traces do not prove arbitrary settings safety, generic GP-confidence validity or global-optimum discovery.']};
fs.writeFileSync('/tmp/modules-gosafe-explorer-implementation19-applied-rerun-result.json',JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({status:report.status,source_sha256:report.source_sha256,all_rollouts:report.all_625_actual_uninterrupted_rollouts,finite_grid_constants:report.finite_grid_constants,gp_initial:report.gp_initial_actual_separate_columns,trace_counts:{safeopt:safeopt.trace.length,gosafeopt:gosafeopt.trace.length}},null,2));
