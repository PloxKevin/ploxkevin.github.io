import { chromium } from '/home/oxrexkevin/SafetyBased/qa/node_modules/playwright-core/index.mjs';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL, fileURLToPath } from 'node:url';
import { settle } from '../../qa/book_browser_checks.mjs';

const SELF = fileURLToPath(import.meta.url);
const ROOT = path.resolve(path.dirname(SELF), '../..');
const report = 'reports/solution-review/source91-landscape-anchor-probe-v1.json';
const planName = 'book/solutions/releases/source91-v1/plan.json';
const plan = JSON.parse(fs.readFileSync(path.join(ROOT, planName)));
const sha = bytes => crypto.createHash('sha256').update(bytes).digest('hex');
const ref = file => ({file, sha256:sha(fs.readFileSync(path.join(ROOT, file)))});
const protectedFiles = [path.relative(ROOT, SELF), planName, 'qa/learning_review.mjs',
  'qa/book_browser_checks.mjs', ...Object.keys(plan.site_source91_sha256).sort()];
const before = protectedFiles.map(ref);
for (const [file, fingerprint] of Object.entries(plan.site_source91_sha256))
  if (ref(file).sha256 !== fingerprint) throw new Error('Source91 asset differs: ' + file);
if (Object.keys(plan.site_source91_sha256).length !== 31) throw new Error('Expected31 assets');
const browser = await chromium.launch({executablePath:process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
const trials = [], errors = [];
const page = await browser.newPage({viewport:{width:1280,height:900}});
page.on('pageerror', e => errors.push(String(e)));
page.on('console', m => { if (m.type()==='error') errors.push(m.text()); });
await page.addInitScript(() => {
  window.__anchorProbe = {events:[], frames:[]};
  const record = type => window.__anchorProbe.events.push({type, t:performance.now(),
    hash:location.hash, ready:document.readyState, fonts:document.fonts.status,
    katexCount:document.querySelectorAll('.katex').length, y:scrollY});
  document.addEventListener('DOMContentLoaded', () => record('DOMContentLoaded'));
  addEventListener('load', () => record('load'));
  addEventListener('hashchange', () => record('hashchange'));
  document.fonts.addEventListener('loading', () => record('fonts_loading'));
  document.fonts.addEventListener('loadingdone', () => record('fonts_loadingdone'));
  document.fonts.ready.then(() => record('initial_fonts_ready'));
  let previous = '';
  function frame() {
    const element = document.getElementById('book-lab');
    if (element) {
      const rect = element.getBoundingClientRect();
      const value = {t:performance.now(), hash:location.hash, y:scrollY,
        top:rect.top, height:rect.height, fonts:document.fonts.status,
        katexCount:document.querySelectorAll('.katex').length};
      const signature = JSON.stringify({...value,t:0});
      if (signature !== previous) {
        window.__anchorProbe.frames.push(value);
        if (window.__anchorProbe.frames.length>800) window.__anchorProbe.frames.shift();
        previous = signature;
      }
    }
    requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
});
const snapshot = () => page.evaluate(() => {
  const target=document.getElementById('book-lab');
  const rect=target?.getBoundingClientRect();
  return {url:location.href,hash:location.hash,t:performance.now(),ready:document.readyState,
    scrollY,innerWidth,innerHeight,documentHeight:document.documentElement.scrollHeight,
    targetCount:document.querySelectorAll('[id="book-lab"]').length,
    rect:rect?{top:rect.top,left:rect.left,width:rect.width,height:rect.height,bottom:rect.bottom}:null,
    fontsStatus:document.fonts.status,fontFaces:[...document.fonts].map(f=>({family:f.family,status:f.status})),
    katexCount:document.querySelectorAll('.katex').length,katexErrors:document.querySelectorAll('.katex-error').length,
    scrollBehavior:getComputedStyle(document.documentElement).scrollBehavior,
    scrollMargin:target?getComputedStyle(target).scrollMarginTop:null,
    targetAnimations:target?.getAnimations().map(a=>({state:a.playState,type:a.constructor.name})),
    resources:performance.getEntriesByType('resource').filter(r=>/katex|woff|components/.test(r.name)).map(r=>({name:r.name,start:r.startTime,duration:r.duration,responseEnd:r.responseEnd}))};
});
async function exactAnchorCheck(record) {
  const start=Date.now();
  const fontsStart=Date.now();
  await page.evaluate(() => document.fonts.ready);
  record.fontReadyWaitMs=Date.now()-fontsStart;
  await settle(page);
  record.beforePredicate=await snapshot();
  try {
    // Same unchanged visibility predicate and5-second timeout as reader QA.
    await page.waitForFunction(hash=>{
      if(decodeURIComponent(location.hash)!==hash)return false;
      const target=document.getElementById(hash.slice(1));if(!target)return false;
      const rect=target.getBoundingClientRect();return rect.top>=-2&&rect.top<innerHeight-20;
    },'#book-lab',{timeout:5000});
    record.status='passed';
  } catch(error) {record.status='failed';record.error=error.message;}
  record.elapsedMs=Date.now()-start;
  record.afterPredicate=await snapshot();
}
try {
  for(let trial=0;trial<3;trial++) {
    await page.goto(pathToFileURL(path.join(ROOT,'SafeLearning/book.html')).href,{waitUntil:'networkidle'});
    const result={trial:trial+1,cache:trial?'same_context_warm':'first_navigation_cold',contents:{},local:{},snapshots:[]};
    await page.locator('.book-contents a[href="landscape.html#book-lab"]').click();
    result.snapshots.push({phase:'after_contents_click',...await snapshot()});
    await exactAnchorCheck(result.contents);
    await page.locator('.book-entry a[href="#book-lab"]').click();
    result.snapshots.push({phase:'after_repeated_fragment_local_click',...await snapshot()});
    await exactAnchorCheck(result.local);
    await settle(page,500);
    result.snapshots.push({phase:'after_extra_500ms_settle',...await snapshot()});
    result.timing=await page.evaluate(()=>window.__anchorProbe);
    const shot='reports/solution-review/source91-landscape-anchor-probe-v1-trial'+(trial+1)+'.png';
    await page.screenshot({path:path.join(ROOT,shot),fullPage:false});
    result.screenshot=ref(shot);
    await page.locator('.book-entry a[href="book.html#book-contents"]').click();
    await page.evaluate(()=>document.fonts.ready);await settle(page);
    result.returnURL=page.url();
    trials.push(result);
  }
} finally {await browser.close();}
const after=protectedFiles.map(ref);
if(JSON.stringify(before)!==JSON.stringify(after))throw new Error('Protected source changed');
const result={status:trials.every(t=>t.contents.status==='passed'&&t.local.status==='passed')&&!errors.length?'passed_focused_navigation_probes':'observed_focused_navigation_failure',
  helper:ref(path.relative(ROOT,SELF)),plan:ref(planName),browserVersion:'145.0.7632.6',
  actualCommand:[process.execPath,path.relative(ROOT,SELF)],cwd:ROOT,
  protectedInputsBefore:before,protectedInputsAfter:after,trials,errors,
  actualSiteOrQAHelperBytesChanged:false,scope:'Observational focused navigation with event/frame probes; original reader QA is rerun separately unchanged.'};
const fd=fs.openSync(path.join(ROOT,report),'wx');
try{fs.writeFileSync(fd,JSON.stringify(result,null,2)+'\n');fs.fsyncSync(fd);}finally{fs.closeSync(fd);}
console.log(JSON.stringify({status:result.status,report:ref(report),trials:trials.map(t=>({trial:t.trial,contents:t.contents.status,local:t.local.status,localFinalRect:t.local.afterPredicate.rect,localMs:t.local.elapsedMs}))}));
if(result.status!=='passed_focused_navigation_probes')process.exitCode=1;
