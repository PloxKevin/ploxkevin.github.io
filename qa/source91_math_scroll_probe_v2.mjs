// Confirm that the full long quantifier display is accessible at390px by user scrolling.
import {chromium} from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {pathToFileURL} from 'node:url';
import {settle} from './book_browser_checks.mjs';
const root='reports/solution-review/source91-math-scroll-v2';
fs.mkdirSync(root,{recursive:true});
if(fs.existsSync(root+'/probe.json'))throw new Error('Use a fresh probe directory');
const sha=name=>crypto.createHash('sha256').update(fs.readFileSync(name)).digest('hex');
const source='SafeLearning/case-studies.html',fingerprint=sha(source);
const browser=await chromium.launch({executablePath:process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try {
  const page=await browser.newPage({viewport:{width:390,height:844}});
  await page.goto(pathToFileURL(path.resolve(source)).href,{waitUntil:'networkidle'});
  await page.waitForFunction(()=>typeof renderMathInElement==='function');
  await page.evaluate(()=>{document.querySelectorAll('details').forEach(d=>d.open=true);return document.fonts.ready;});
  const boxTarget=page.locator('#book-project-tank-b3 .math-block').first();
  const math=boxTarget.locator('.katex-display').first();
  await math.scrollIntoViewIfNeeded();await settle(page,450);
  const read=()=>math.evaluate(el=>({overflowX:getComputedStyle(el).overflowX,clientWidth:el.clientWidth,scrollWidth:el.scrollWidth,scrollLeft:el.scrollLeft,mathErrors:el.querySelectorAll('.katex-error').length}));
  const before=await read();
  const box=await math.boundingBox();await page.mouse.move(box.x+box.width/2,box.y+box.height/2);
  await page.mouse.wheel(1200,0);await settle(page,450);
  const after=await read();
  const image=root+'/quantifiers-scrolled-right-390.png';await boxTarget.screenshot({path:image,animations:'disabled'});
  const passed=['auto','scroll'].includes(before.overflowX)&&before.scrollWidth>before.clientWidth&&after.scrollLeft>0&&after.scrollLeft+after.clientWidth>=after.scrollWidth-2&&after.mathErrors===0&&sha(source)===fingerprint;
  const report={status:passed?'passed_actual_user_horizontal_math_scrolling':'failed_scroll_probe',source,source_sha256:fingerprint,before,after,gesture:'Actual horizontal mouse wheel at the math box, deltaX1200',screenshot:{file:image,sha256:sha(image)},scope:'Actual user gesture in the inner KaTeX display scroll container; acceptance requires both ends accessible and no math rendering errors.'};
  fs.writeFileSync(root+'/probe.json',JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify(report));if(!passed)process.exitCode=1;
} finally {await browser.close();}
