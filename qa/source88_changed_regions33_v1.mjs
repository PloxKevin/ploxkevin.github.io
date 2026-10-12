// Fresh captures of the exact Source88 qualified lesson regions, without site edits.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { settle, renderedMathProblems } from './book_browser_checks.mjs';

const root = process.cwd();
const report = path.join(root, 'reports/full-coverage/browser33-source88-changed-regions-v1.json');
const artifacts = path.join(root, 'reports/full-coverage/browser33-source88-changed-region-artifacts-v1');
if (fs.existsSync(report) || fs.existsSync(artifacts)) throw new Error('Use fresh report and capture paths');
const sha = p => crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const ref = p => ({file:path.relative(root,p),sha256:sha(p),bytes:fs.statSync(p).size});
const targets = [
  {file:'primer-basics.html', label:'rate-definitions916918', selector:'.definition-box', text:'Linear, sublinear and quadratic convergence', keys:['primer-basics.html::node-916','primer-basics.html::node-918']},
  {file:'primer-basics.html', label:'rate-envelopes922', selector:'p', text:'the geometric envelope', keys:['primer-basics.html::node-922']},
  {file:'primer-linalg.html', label:'positive-subunit-p171', selector:'.warning-box', text:'the formula is not a norm', keys:['primer-linalg.html::node-171']},
  {file:'primer-linalg.html', label:'cube-covering191', selector:'p', text:'Covering numbers.', keys:['primer-linalg.html::node-191']},
  {file:'primer-linalg.html', label:'signed-Hausdorff205', selector:'p', text:'Signed distance and Hausdorff distance.', keys:['primer-linalg.html::node-205']},
  {file:'primer-linalg.html', label:'common-norms305307', selector:'.definition-box', text:'Formulas for the common induced norms', keys:['primer-linalg.html::node-305','primer-linalg.html::node-307']},
  {file:'primer-linalg.html', label:'common-norm-proofs311', selector:'p', text:'the longest semi-axis', keys:['primer-linalg.html::node-311']},
  {file:'primer-linalg.html', label:'box-zonotope332', selector:'p', text:'The image of a box is a zonotope.', keys:['primer-linalg.html::node-332']},
  {file:'primer-linalg.html', label:'planar-conics529', selector:'p', text:'for the zero matrix this level set is empty', keys:['primer-linalg.html::node-529']}
];
const expected = {
  'SafeLearning/primer-basics.html':'f9b6d6adb95fb3c261768d3dc581046f7bc13e5d8c8223fd52e8ae219c68a300',
  'SafeLearning/primer-linalg.html':'6b84e56764f72ca29d8626dd328a0c55490d63a1ca95ed1d5e5d349aaf642d25'
};
const before = Object.fromEntries(Object.keys(expected).map(n=>[n,sha(path.join(root,n))]));
if (JSON.stringify(before)!==JSON.stringify(expected)) throw new Error('Expected exact Source88 page bytes');
const results=[];
fs.mkdirSync(artifacts,{recursive:true});
const browser = await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM || process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
  for (const t of targets) {
    const page = await browser.newPage({viewport:{width:1280,height:900}});
    const runtime=[];
    page.on('pageerror',error=>runtime.push(error.message));
    page.on('console',message=>{if(message.type()==='error')runtime.push(message.text());});
    try {
      await page.goto(pathToFileURL(path.join(root,'SafeLearning',t.file)).href,{waitUntil:'networkidle'});
      await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
      const target = page.locator(t.selector).filter({hasText:t.text});
      if (await target.count()!==1) throw new Error('Changed region must be unique: '+t.label);
      await target.evaluate(el=>{
        for (let n=el;n;n=n.parentElement) {
          if(n.matches('details'))n.open=true;
          if(n.matches('.collapsible'))n.classList.add('open');
        }
      });
      for(const width of [360,1280]) {
        await page.setViewportSize({width,height:900});
        await page.evaluate(()=>document.fonts.ready);
        await settle(page,350);
        await page.waitForFunction(()=>{
          const main=document.querySelector('.main-content');
          return !main || !main.getAnimations().some(a=>a instanceof CSSTransition && a.playState==='running');
        },null,{timeout:5000});
        const errors=await target.evaluate(renderedMathProblems);
        const box=await target.boundingBox();
        if(!box || box.height<=0)throw new Error('Changed region must be visible: '+t.label);
        const layout=await target.evaluate(el=>({clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,
          documentWidth:document.documentElement.scrollWidth,viewportWidth:innerWidth,
          text:el.innerText,katexCount:el.querySelectorAll('.katex').length}));
        if(layout.documentWidth>width+8)errors.push('Page overflow: '+layout.documentWidth+' at'+width);
        const filename=path.join(artifacts,t.label+'-'+width+'.png');
        await target.screenshot({path:filename,animations:'disabled',style:'.sidebar-open,.skip-link { visibility:hidden !important; }'});
        results.push({file:t.file,region:t.label,source_unit_keys:t.keys,selector:t.selector,
          unique_text:t.text,viewportWidth:width,status:errors.length || runtime.length?'failed':'passed',
          errors,runtimeErrors:[...runtime],source_sha256:before['SafeLearning/'+t.file],
          capture:ref(filename),dimensions:box,layout,visualInspection:'pending',
          scope:'Exact changed lesson excerpt and inherited-context proof paragraph only. No complete mathematical coverage, full explorer semantics or whole-page visual review is inferred.'});
      }
    } finally {await page.close();}
  }
} finally {await browser.close();}
const after=Object.fromEntries(Object.keys(expected).map(n=>[n,sha(path.join(root,n))]));
if(JSON.stringify(before)!==JSON.stringify(after))throw new Error('Source changed during captures');
const passed=results.length===18 && results.every(r=>r.status==='passed');
fs.writeFileSync(report,JSON.stringify({status:passed?'passed':'failed',helper:ref(path.join(root,'qa/source88_changed_regions33_v1.mjs')),
  shared_check_helper:ref(path.join(root,'qa/book_browser_checks.mjs')),source_sha256_before:before,
  source_sha256_after:after,source_bytes_preserved:true,results,visualInspection:'pending',coverage_complete:false},null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({report:path.relative(root,report),captures:results.length,status:passed?'passed':'failed'}));
if(!passed)process.exitCode=1;
