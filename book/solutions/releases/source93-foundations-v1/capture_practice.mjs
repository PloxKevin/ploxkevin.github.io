// Capture the actual new and rewritten practice at two reading widths.
import {chromium} from '../../../../qa/node_modules/playwright-core/index.mjs';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {fileURLToPath,pathToFileURL} from 'node:url';

const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'../../../..');
const source=path.join(root,'SafeLearning/primer-basics.html');
const out=path.join(root,'reports/solution-review/source93-practice-visual-v1');
fs.mkdirSync(out,{recursive:true});
const sha=data=>crypto.createHash('sha256').update(data).digest('hex');
const sourceHash=sha(fs.readFileSync(source));
const browser=await chromium.launch({executablePath:process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
const shots=[];
for (const width of [390,1280]) {
  const page=await browser.newPage({viewport:{width,height:900}});
  await page.goto(pathToFileURL(source).href,{waitUntil:'networkidle'});
  await page.waitForFunction(()=>typeof window.renderMathInElement==='function');
  await page.evaluate(()=>document.querySelectorAll('details').forEach(d=>d.open=true));
  for (const code of ['0.W2','0.GS4','0.GF4','0.5c']) {
    const target=page.locator('details').filter({has:page.locator(':scope > summary').filter({hasText:'Exercise '+code+' —'})});
    // Use the unique direct exercise summary so no ancestor is captured.
    const summary=page.locator('summary').filter({hasText:new RegExp('^Exercise '+code.replaceAll('.','\\.')+' [—–]')});
    const exercise=summary.locator('..');
    if (await exercise.count()!==1) throw new Error('Ambiguous exercise '+code);
    const name=code.replaceAll('.','-')+'-'+width+'.png';
    const filename=path.join(out,name);
    await exercise.screenshot({path:filename,animations:'disabled',style:'.sidebar-open,.skip-link {visibility:hidden !important;}'});
    const data=fs.readFileSync(filename);
    shots.push({exercise:code,width,path:path.relative(root,filename),sha256:sha(data),bytes:data.length,source_sha256:sourceHash,visualInspection:'pending'});
  }
  await page.close();
}
await browser.close();
if (sha(fs.readFileSync(source))!==sourceHash) throw new Error('Source changed during capture');
fs.writeFileSync(path.join(out,'manifest.json'),JSON.stringify({status:'captured',source:'SafeLearning/primer-basics.html',source_sha256:sourceHash,shots},null,2)+'\n');
console.log(JSON.stringify({status:'captured',shots:shots.length}));
