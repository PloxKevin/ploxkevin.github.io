// Capture readable final explorer and worked-answer views, bound to Source91 hashes.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { settle } from './book_browser_checks.mjs';

const plan = JSON.parse(fs.readFileSync('book/solutions/releases/source91-v1/plan.json'));
const root = 'reports/solution-review/source91-visual-v1';
const reportFile = root + '/captures.json';
if (fs.existsSync(reportFile)) throw new Error('Use a fresh visual artifact directory');
fs.mkdirSync(root, {recursive:true});
const hash = filename => crypto.createHash('sha256').update(fs.readFileSync(filename)).digest('hex');
const pages = [...new Set(plan.files.filter(r=>r.file.startsWith('SafeLearning/')).map(r=>r.file))].sort();
const report = {status:'running',scope:'Actual readable viewport captures; visual inspection remains a separate explicit review.',helper_sha256:hash('qa/solution_visual91.mjs'),pages:[]};
const write = () => {const temporary=reportFile+'.tmp';fs.writeFileSync(temporary,JSON.stringify(report,null,2)+'\n');fs.renameSync(temporary,reportFile);};
write();
const browser = await chromium.launch({executablePath:process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
  for (const source of pages) {
    const expected=plan.site_source91_sha256[source];
    if(hash(source)!==expected)throw new Error('Source differs: '+source);
    const page=await browser.newPage({viewport:{width:1280,height:900}});
    const row={source,source_sha256:expected,captures:[],runtimeErrors:[]};report.pages.push(row);write();
    page.on('pageerror',e=>row.runtimeErrors.push(e.message));
    await page.goto(pathToFileURL(path.resolve(source)).href,{waitUntil:'networkidle'});
    await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
    await page.evaluate(()=>document.fonts.ready);
    const stem=path.basename(source,'.html');
    if(stem==='verification') {
      row.actualPanelAExamples=[];
      for(const sample of [
        {eps:.5,expected:['IBP [−7.00, 3.00]','CROWN (adaptive','[−5.00, 1.00]','exact [−5.00, 1.00]']},
        {eps:1.5,expected:['IBP [−12.00, 13.00]','[−11.00, 7.00]','α-CROWN [−8.50, 7.00]','exact [−8.50, 7.00]']}
      ]) {
        await page.evaluate(eps=>{
          for(const [key,value] of Object.entries({w11:1,w12:1,w21:-1,w22:2,b1:1,b2:1,v1:-2,v2:2,eps}))document.getElementById('vfa-'+key).value=String(value);
          document.getElementById('vfa-eps').dispatchEvent(new Event('input',{bubbles:true}));
        },sample.eps);
        await settle(page,350);
        const readout=await page.locator('#vfa-info').innerText();
        const passed=sample.expected.every(text=>readout.includes(text));
        row.actualPanelAExamples.push({epsilon:sample.eps,expected:sample.expected,actualReadout:readout,passed});
        if(!passed)throw new Error('Actual Panel A differs from the worked example at epsilon '+sample.eps);
      }
    }
    const explorer=page.locator('.interactive-container').filter({has:page.locator('input[type=range]')}).first();
    row.hasExistingSliderExplorer=!!await explorer.count();
    if(row.hasExistingSliderExplorer) {
      await explorer.scrollIntoViewIfNeeded();await settle(page,350);
      const filename=root+'/'+stem+'-explorer-1280.png';
      await explorer.screenshot({path:filename,animations:'disabled'});
      row.captures.push({kind:'explorer',width:1280,file:filename,sha256:hash(filename)});
    }
    await page.setViewportSize({width:390,height:844});
    await page.evaluate(()=>{document.querySelectorAll('.collapsible').forEach(c=>c.classList.add('open'));document.querySelectorAll('details').forEach(d=>d.open=true);});
    await settle(page,450);
    const answer = await page.evaluate(() => {
      const all=[...document.querySelectorAll('details')];
      const targets=all.filter(d=>/^(Show .*?(answer|solution)|Show answer|Show solution|Worked solution)/i.test(d.querySelector(':scope > summary')?.textContent.trim()||''));
      // Prefer a substantive newly expanded answer over a tiny readiness box.
      const selected=targets.map(d=>({d,length:d.innerText.length})).sort((a,b)=>b.length-a.length)[0];
      if(!selected)return null;
      const ancestors=[];let ancestor=selected.d.parentElement?.closest('details');
      while(ancestor){ancestors.push(ancestor.querySelector(':scope > summary')?.textContent.trim()||'');ancestor=ancestor.parentElement?.closest('details');}
      return {detailIndex:all.indexOf(selected.d),summary:selected.d.querySelector(':scope > summary').textContent.trim(),
              ancestors,textLength:selected.length,selectionPurpose:'Choose a readable long-answer viewport; length does not assess pedagogical adequacy.'};
    });
    if(!answer)throw new Error('No worked-answer target on '+source);
    row.answerSelection=answer;
    const target=page.locator('details').nth(answer.detailIndex);
    if(await target.count()) {
      await target.scrollIntoViewIfNeeded();await settle(page,350);
      const box=await target.boundingBox();
      // A clipped viewport image keeps text at original readable resolution.
      await page.evaluate(y=>scrollTo({top:y,behavior:'instant'}),Math.max(0,await target.evaluate(e=>e.getBoundingClientRect().top+scrollY)));
      await settle(page,250);
      const filename=root+'/'+stem+'-solution-390.png';
      await page.screenshot({path:filename,fullPage:false,animations:'disabled',style:'.sidebar-open,.skip-link{visibility:hidden!important}'});
      row.captures.push({kind:'worked_solution_viewport',width:390,file:filename,sha256:hash(filename),targetDimensions:box});
    }
    if(hash(source)!==expected)throw new Error('Source changed during capture');
    await page.close();write();
  }
  report.status=report.pages.length===22&&report.pages.every(r=>r.runtimeErrors.length===0
    &&r.captures.some(c=>c.kind==='worked_solution_viewport')
    &&(!r.hasExistingSliderExplorer||r.captures.some(c=>c.kind==='explorer')))?'captured_actual_source91_views_inspection_pending':'failed_capture';write();
} finally {await browser.close();}
console.log(JSON.stringify({status:report.status,pages:report.pages.length,report:reportFile}));
if(report.status==='failed_capture')process.exitCode=1;
