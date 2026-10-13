// Fresh Source90 lesson captures and a clearly bounded prose-derived scalar evaluator.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';

const root = process.cwd();
const out = path.join(root, 'book/coverage/checks/checkpoint34-review');
const { chromium } = await import(pathToFileURL(path.join(root,'qa/node_modules/playwright-core/index.mjs')).href);
const { settle, renderedMathProblems } = await import(pathToFileURL(path.join(root,'qa/book_browser_checks.mjs')).href);
const reportPath = path.join(out,'browser34-source90-five-changed-regions-v1.json');
const finitePath = path.join(out,'browser34-source90-prose-derived-scalar-two-finite-trajectories-v1.json');
const artifacts = path.join(out,'browser34-source90-changed-region-artifacts-v1');
for (const file of [reportPath,finitePath,artifacts]) if (fs.existsSync(file)) throw new Error('Fresh outputs required: '+file);
const sha = file => crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
const hash = value => crypto.createHash('sha256').update(value).digest('hex');
const ref = file => ({file:path.relative(root,file),sha256:sha(file),bytes:fs.statSync(file).size});
const expected = {
  'SafeLearning/nn-in-the-loop.html':'22b785e46001e4e5d73166d05503f9beb5454634cfa6b929df24f6bbe33e7e4b',
  'SafeLearning/primer-probability.html':'19891bd487ec19b67cbda477809a3a273242c6d4b0647e93c01b94f75108519f'
};
for (const [name,value] of Object.entries(expected)) if (sha(path.join(root,name)) !== value) throw new Error('Source90 hash mismatch: '+name);
const inventory = JSON.parse(fs.readFileSync(path.join(root,'book/coverage/inventory-after-correction90.json'),'utf8'));
const targets = [
  {file:'nn-in-the-loop.html',label:'NN14_3-question1210',selector:'p',text:'find the supremal open interval',key:'nn-in-the-loop.html::node-1210'},
  {file:'nn-in-the-loop.html',label:'NN14_3-global1217',selector:'p',text:'with exact eigenvalues',key:'nn-in-the-loop.html::node-1217'},
  {file:'nn-in-the-loop.html',label:'NN14_3-open-basin1218',selector:'p',text:'The supremal radius',key:'nn-in-the-loop.html::node-1218'},
  {file:'nn-in-the-loop.html',label:'NN14_3-exact-box1220',selector:'p',text:'An explicit simple feasible choice',key:'nn-in-the-loop.html::node-1220'},
  {file:'primer-probability.html',label:'conditional-mean-version387',selector:'.definition-box',text:'Conditional expectation and the tower rule',key:'primer-probability.html::node-387'}
];
fs.mkdirSync(artifacts);
const results=[];
const browser = await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM || process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
let finite;
try {
  for (const file of ['nn-in-the-loop.html','primer-probability.html']) {
    const page = await browser.newPage({viewport:{width:1280,height:900}});
    const runtime=[];
    page.on('pageerror',error=>runtime.push(error.message));
    page.on('console',message=>{if(message.type()==='error')runtime.push(message.text());});
    try {
      await page.goto(pathToFileURL(path.join(root,'SafeLearning',file)).href,{waitUntil:'networkidle'});
      await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
      for (const target of targets.filter(target=>target.file===file)) {
        const locator=page.locator(target.selector).filter({hasText:target.text});
        if(await locator.count()!==1)throw new Error('Unique actual changed region required: '+target.label);
        await locator.evaluate(el=>{for(let node=el;node;node=node.parentElement){if(node.matches('details'))node.open=true;if(node.matches('.collapsible'))node.classList.add('open');}});
        const literal=inventory.material_source_units.find(row=>row.key===target.key);
        if(!literal || literal.source_sha256!==expected['SafeLearning/'+file])throw new Error('Exact Source90 inventory literal required');
        for(const width of [360,1280]) {
          await page.setViewportSize({width,height:900});
          await page.evaluate(()=>document.fonts.ready);
          await settle(page,350);
          await page.waitForFunction(()=>{const main=document.querySelector('.main-content');return !main || !main.getAnimations().some(a=>a instanceof CSSTransition && a.playState==='running');},null,{timeout:5000});
          const errors=await locator.evaluate(renderedMathProblems);
          const dimensions=await locator.boundingBox();
          if(!dimensions || dimensions.height<=0)throw new Error('Visible changed region required');
          const layout=await locator.evaluate(el=>({clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,documentWidth:document.documentElement.scrollWidth,viewportWidth:innerWidth,text:el.innerText,katexCount:el.querySelectorAll('.katex').length}));
          if(layout.documentWidth>width+8)errors.push('Page overflow: '+layout.documentWidth+' at '+width);
          const capture=path.join(artifacts,target.label+'-'+width+'.png');
          await locator.screenshot({path:capture,animations:'disabled',style:'.sidebar-open,.skip-link {visibility:hidden !important;}'});
          results.push({file,key:target.key,region:target.label,selector:target.selector,unique_text:target.text,
                        viewportWidth:width,status:errors.length||runtime.length?'failed':'passed',errors,runtimeErrors:[...runtime],
                        source_sha256:expected['SafeLearning/'+file],literal_text_sha256:literal.text_sha256,
                        capture:ref(capture),dimensions,layout,visualInspection:'pending',
                        scope:'Actual changed lesson excerpt at this width; no complete mathematical coverage or whole explorer semantics inferred.'});
        }
      }
      if(file==='nn-in-the-loop.html') {
        const source=fs.readFileSync(path.join(root,'SafeLearning',file),'utf8');
        const literal=inventory.material_source_units.find(row=>row.key==='nn-in-the-loop.html::node-1218');
        const expression=/x\^\+=([0-9.]+)x-([0-9.]+)\\tanh\(([0-9.]+)x\)/g;
        const matches=[...literal.source_text.matchAll(expression)];
        if(matches.length!==1)throw new Error('Unique current literal scalar map required');
        const match=matches[0];
        const coefficients={a:Number(match[1]),gain:Number(match[2]),weight:Number(match[3])};
        if(coefficients.a!==1.3 || coefficients.gain!==0.6 || coefficients.weight!==2)throw new Error('Reviewed scalar coefficients required');
        const seeds=[...literal.source_text.matchAll(/x_0=([0-9.]+)/g)].map(m=>Number(m[1]));
        if(JSON.stringify(seeds)!==JSON.stringify([1.9985,1.999]))throw new Error('Exact two current source initials required');
        const actual=await page.evaluate(({coefficients,seeds,steps})=>{
          const step=x=>coefficients.a*x-coefficients.gain*Math.tanh(coefficients.weight*x);
          return {evaluator_source:step.toString(),trajectories:seeds.map(initial=>{
            const states=[initial];for(let i=0;i<steps;i++)states.push(step(states.at(-1)));
            return {initial,step_count:steps,state_count:states.length,states,all_states_finite:states.every(Number.isFinite),
                    final:states.at(-1),maximum_absolute_state:Math.max(...states.map(Math.abs)),
                    observed_monotone_decrease:states.every((x,i)=>!i||x<=states[i-1]),observed_monotone_increase:states.every((x,i)=>!i||x>=states[i-1])};
          })};
        },{coefficients,seeds,steps:200});
        const pageScripts=[...source.matchAll(/<script\b([^>]*)>([\s\S]*?)<\/script>/g)].map((m,i)=>({ordinal_1_based:i+1,attributes:m[1],script_text_sha256:hash(m[2]),bytes:Buffer.byteLength(m[2])}));
        const actual2D=source.match(/function stepf\(S, x\) \{[^\n]*\}/)?.[0];
        if(!actual2D || !actual2D.includes('return [x[0] + H * x[1]'))throw new Error('Actual page simulator domain must be identified');
        const finitePassed=actual.trajectories.length===2 && actual.trajectories.every(t=>t.state_count===201&&t.all_states_finite) && actual.trajectories[0].observed_monotone_decrease && actual.trajectories[1].observed_monotone_increase;
        finite={status:finitePassed?'passed_actual_source_prose_derived_two_finite_scalar_browser_JS_trajectories':'failed',
          checked_at_utc:new Date().toISOString(),source:ref(path.join(root,'SafeLearning',file)),
          current_literal_key:literal.key,current_literal_text_sha256:literal.text_sha256,exact_prose_scalar_map:match[0],
          coefficients_derived_from_current_prose:coefficients,initial_states_derived_from_current_prose:seeds,
          evaluator_kind:'Independent prose-derived evaluator executed by genuine browser JavaScript; this scalar evaluator is not a page function.',
          actual_browser_evaluator_source:actual.evaluator_source,actual_current_page_script_digests:pageScripts,
          actual_current_page_2D_stepf_source_sha256:hash(actual2D),actual_page_2D_stepf_was_used_for_scalar_trajectory:false,
          trajectories:actual.trajectories,helper:ref(path.join(out,'source90_changed_regions_and_scalar_finite34_v1.mjs')),
          finite_scope:'All201 floating-point states of each exact printed initial constant over200steps. No floating-point error bound or infinite-time theorem is attributed to this evaluator.',
          all_time_convergence_divergence_theorem_receipt:false,default_2D_Exercise14_4_explorer_correctness_receipt:false,
          whole_universal_scalar_scope_is_in_the_separate_exact_Lean65_source:true,coverage_complete:false};
      }
    } finally {await page.close();}
  }
} finally {await browser.close();}
for(const [name,value] of Object.entries(expected))if(sha(path.join(root,name))!==value)throw new Error('Source changed during actual captures/evaluation');
if(!finite)throw new Error('Finite scalar evaluator was not executed');
fs.writeFileSync(finitePath,JSON.stringify(finite,null,2)+'\n',{flag:'wx'});
const passed=results.length===10&&results.every(result=>result.status==='passed');
fs.writeFileSync(reportPath,JSON.stringify({status:passed?'passed':'failed',source90_pages_sha256:expected,results,
  helper:ref(path.join(out,'source90_changed_regions_and_scalar_finite34_v1.mjs')),shared_check_helper:ref(path.join(root,'qa/book_browser_checks.mjs')),
  source_bytes_preserved:true,finite_scalar_receipt:ref(finitePath),visualInspection:'pending',coverage_complete:false},null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({report:ref(reportPath),captures:results.length,finite_scalar_receipt:ref(finitePath),status:passed?'passed':'failed'}));
if(!passed || finite.status==='failed')process.exitCode=1;
