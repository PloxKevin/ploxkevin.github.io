// Check actual horizontal wheel access to overflowing captured-region mathematics.
import { createRequire } from 'node:module';
const require=createRequire(new URL('../../../qa/learning_review.mjs',import.meta.url));
const { chromium }=require('playwright-core');
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
const root=process.cwd();
const reports=path.join(root,'reports/full-coverage');
const output=path.join(reports,'source60-four-page-math-scroll28-v2.json');
if(fs.existsSync(output)) throw new Error('Use a new output record');
const digest=p=>crypto.createHash('sha256').update(fs.readFileSync(path.join(root,p))).digest('hex');
const original=JSON.parse(fs.readFileSync(path.join(reports,'browser-checkpoint-28.json')));
const before={...original.source_sha256};
for(const [p,h] of Object.entries(before))if(digest(p)!==h)throw new Error('Source changed: '+p);
const snapshot=path.join(reports,'browser-input28-source60/SafeLearning');
for(const [p,h] of Object.entries(before))if(digest(path.relative(root,path.join(snapshot,path.basename(p))))!==h)throw new Error('Snapshot differs: '+p);
const record={status:'running',started_at_utc:new Date().toISOString(),scope:'Actual horizontal mouse-wheel access to overflow mathematics in the four source60 book-lab regions at390px. No whole-chapter or mathematical proof claim.',source_sha256:before,pages:[],errors:[]};
fs.writeFileSync(output,JSON.stringify(record,null,2)+'\n',{flag:'wx'});
const browser=await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM || process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
 for(const file of ['lyapunov-mpc.html','verification.html','primer-probability.html','lipsdp.html']){
  const page=await browser.newPage({viewport:{width:390,height:900}});
  const r={file,status:'running',overflow_containers:[],errors:[]};record.pages.push(r);
  await page.goto(pathToFileURL(path.join(snapshot,file)).href,{waitUntil:'networkidle'});
  await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
  await page.evaluate(()=>document.querySelectorAll('#book-lab details').forEach(d=>d.open=true));
  await page.waitForTimeout(150);
  const indices=await page.locator('#book-lab .katex-display, #book-lab .math-scroll, #book-lab .math-scroll-xs').evaluateAll(els=>els.flatMap((el,i)=>{
   const style=getComputedStyle(el);return el.clientWidth>0 && el.scrollWidth>el.clientWidth+2 && ['auto','scroll'].includes(style.overflowX)?[i]:[];
  }));
  if(!indices.length)r.errors.push('No expected overflow container found');
  for(const i of indices){
   const loc=page.locator('#book-lab .katex-display, #book-lab .math-scroll, #book-lab .math-scroll-xs').nth(i);
   await loc.scrollIntoViewIfNeeded();await loc.evaluate(el=>el.scrollLeft=0);
   const initial=await loc.evaluate(el=>({clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,scrollLeft:el.scrollLeft,text:el.textContent.trim().slice(0,180)}));
   await loc.hover();await page.mouse.wheel(4000,0);await page.waitForTimeout(160);
   const right=await loc.evaluate(el=>el.scrollLeft);
   await page.mouse.wheel(-4000,0);await page.waitForTimeout(160);
   const left=await loc.evaluate(el=>el.scrollLeft);
   const passed=right>initial.scrollLeft+1 && Math.abs(right-(initial.scrollWidth-initial.clientWidth))<=2 && Math.abs(left)<=2;
   r.overflow_containers.push({locator_index:i,...initial,actual_wheel_right_scrollLeft:right,actual_wheel_left_scrollLeft:left,status:passed?'passed':'failed'});
   if(!passed)r.errors.push('Actual horizontal wheel did not traverse both ends: '+i);
  }
  r.status=r.errors.length?'failed':'passed';record.errors.push(...r.errors.map(e=>file+': '+e));await page.close();
 }
} finally {await browser.close();}
for(const [p,h] of Object.entries(before))if(digest(p)!==h)record.errors.push('Source changed during run: '+p);
record.finished_at_utc=new Date().toISOString();record.status=record.errors.length?'failed':'passed';
record.actual_overflow_container_count=record.pages.reduce((n,p)=>n+p.overflow_containers.length,0);
fs.writeFileSync(output,JSON.stringify(record,null,2)+'\n');
console.log(JSON.stringify({status:record.status,pages:record.pages.length,actual_overflow_container_count:record.actual_overflow_container_count,errors:record.errors}));
if(record.errors.length)process.exitCode=1;
