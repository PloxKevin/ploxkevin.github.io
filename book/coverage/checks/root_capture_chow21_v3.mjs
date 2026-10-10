import {chromium} from '../../../qa/node_modules/playwright-core/index.mjs';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {pathToFileURL} from 'node:url';
const root=process.cwd();
const source=path.join(root,'reports/full-coverage/browser-input21-source48/SafeLearning/lyapunov-mpc.html');
const output=path.join(root,'reports/full-coverage/chow21-rendered-exercise-capture-v3.json');
const hash=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
if(fs.existsSync(output))throw new Error('Preserve existing evidence');
const started=new Date().toISOString(), before=hash(source), rows=[],errors=[];
const browser=await chromium.launch({executablePath:process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
 for(const width of [390,1280]){
  const page=await browser.newPage({viewport:{width,height:900}});
  page.on('pageerror',e=>errors.push(String(e)));
  await page.goto(pathToFileURL(source).href,{waitUntil:'networkidle'});
  await page.waitForFunction(()=>typeof window.renderMathInElement==='function');
  const exercise=page.locator('summary').filter({hasText:'Exercise 11.5'}).first().locator('..');
  if(await exercise.count()!==1)throw new Error('Missing exact Chow exercise');
  await exercise.evaluate(el=>{el.open=true;for(const d of el.querySelectorAll('details'))d.open=true;});
  await page.evaluate(()=>document.fonts.ready);
  const text=await exercise.innerText();
  const katexErrors=await exercise.locator('.katex-error').count();
  if(katexErrors)errors.push('KaTeX errors at '+width+': '+katexErrors);
  const target=path.join(root,'reports/full-coverage/browser-artifacts-source48-21-v1/chow115-'+width+'.png');
  if(fs.existsSync(target))throw new Error('Preserve existing capture');
  await exercise.screenshot({path:target,animations:'disabled',style:'.skip-link, .sidebar-open, .sidebar { visibility: hidden !important; }'});
  rows.push({width,path:path.relative(root,target),sha256:hash(target),source_sha256:before,katexErrors,rendered_exercise_text:text});
  await page.close();
 }
}finally{await browser.close();}
const after=hash(source);if(after!==before)errors.push('Source changed');
fs.writeFileSync(output,JSON.stringify({status:errors.length?'failed':'passed_actual_targeted_rendered_capture',started_at_utc:started,finished_at_utc:new Date().toISOString(),source:path.relative(root,source),source_sha256_before:before,source_sha256_after:after,helper_sha256:hash(path.join(root,'book/coverage/checks/root_capture_chow21_v3.mjs')),captures:rows,errors,capture_only_style:'.skip-link, .sidebar-open, .sidebar { visibility: hidden !important; }',scope:'Actual two-width screenshot of the fully expanded current48 Chow question and all answers. Fixed navigation is temporarily hidden only in capture to prevent long-element screenshot overlays. Source bytes and layout widths remain exact. Manual visual review is a separate observation.'},null,2)+'\n');
if(errors.length)throw new Error(errors.join(';'));
console.log(JSON.stringify({status:'passed',captures:rows.length}));
