// Capture the two corrected original lesson regions, separate from application labs.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { settle, renderedMathProblems } from './book_browser_checks.mjs';

const root = process.cwd();
const report = path.join(root, 'reports/full-coverage/browser31-source81-two-changed-regions-v1.json');
const artifacts = path.join(root, 'reports/full-coverage/browser-artifacts-31-source81-changed-regions-v1');
if (fs.existsSync(report) || fs.existsSync(artifacts)) throw new Error('Use fresh report and capture paths');
const sha = p => crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const targets = [
  {file:'primer-linalg.html', label:'spectral-induction-proof-sketch', selector:'.collapsible', text:'Proof sketch — a full orthonormal eigenbasis'},
  {file:'nn-in-the-loop.html', label:'integral-tracking-Exercise14.5', selector:'details', text:'Exercise 14.5 — Offset-free tracking'}
];
const before = Object.fromEntries(targets.map(t=>['SafeLearning/'+t.file,sha(path.join(root,'SafeLearning',t.file))]));
const results = [];
fs.mkdirSync(artifacts,{recursive:true});
const browser = await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM || process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
  for (const t of targets) {
    const page = await browser.newPage();
    try {
      await page.goto(pathToFileURL(path.join(root,'SafeLearning',t.file)).href,{waitUntil:'networkidle'});
      await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
      const target = page.locator(t.selector).filter({hasText:t.text});
      if (await target.count() !== 1) throw new Error('Changed region must be unique: '+t.label);
      await target.evaluate(el=>{
        for (let n=el;n;n=n.parentElement) {
          if (n.matches('details')) n.open=true;
          if (n.matches('.collapsible')) n.classList.add('open');
        }
        el.querySelectorAll('details').forEach(d=>d.open=true);
        el.querySelectorAll('.collapsible').forEach(d=>d.classList.add('open'));
      });
      for (const width of [360,1280]) {
        await page.setViewportSize({width,height:900});
        await page.evaluate(()=>document.fonts.ready);
        await settle(page);
        const errors = await target.evaluate(renderedMathProblems);
        const filename = path.join(artifacts,t.label+'-'+width+'.png');
        const bounds = await target.boundingBox();
        if (!bounds || bounds.height<=0) throw new Error('Changed region must be visible');
        await target.screenshot({path:filename,animations:'disabled',style:'.sidebar-open,.skip-link { visibility:hidden !important; }'});
        results.push({file:t.file,region:t.label,viewportWidth:width,status:errors.length?'failed':'passed',errors,
          source_sha256:before['SafeLearning/'+t.file],capture:{file:path.relative(root,filename),sha256:sha(filename),bytes:fs.statSync(filename).size},
          dimensions:bounds,visualInspection:'pending',scope:'Only this original corrected lesson region; whole-page and application-lab visual coverage is not claimed.'});
      }
    } finally { await page.close(); }
  }
} finally { await browser.close(); }
if (Object.entries(before).some(([n,h])=>sha(path.join(root,n))!==h)) throw new Error('Source changed during captures');
fs.writeFileSync(report,JSON.stringify({status:results.length===4 && results.every(r=>r.status==='passed')?'passed':'failed',
  helper_sha256:sha(path.join(root,'qa/source81_changed_regions31_v1.mjs')),source_sha256:before,results,visualInspection:'pending',coverage_complete:false},null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({report:path.relative(root,report),captures:results.length,status:results.every(r=>r.status==='passed')?'passed':'failed'}));
if (results.some(r=>r.status!=='passed')) process.exitCode=1;
