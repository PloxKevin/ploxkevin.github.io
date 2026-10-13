// Check the deliberately scrollable long matrix/QC at the changed mobile regions.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
const root=process.cwd(),out=path.join(root,'book/coverage/checks/checkpoint34-review');
const {chromium}=await import(pathToFileURL(path.join(root,'qa/node_modules/playwright-core/index.mjs')).href);
const {settle}=await import(pathToFileURL(path.join(root,'qa/book_browser_checks.mjs')).href);
const sha=p=>crypto.createHash('sha256').update(fs.readFileSync(p)).digest('hex');
const ref=p=>({file:path.relative(root,p),sha256:sha(p),bytes:fs.statSync(p).size});
const report=path.join(out,'browser34-source90-mobile-formula-scroll-v1.json');
if(fs.existsSync(report))throw new Error('Fresh output required');
const targets=[
  {file:'nn-in-the-loop.html',sha256:'22b785e46001e4e5d73166d05503f9beb5454634cfa6b929df24f6bbe33e7e4b',selector:'p',text:'An explicit simple feasible choice',key:'nn-in-the-loop.html::node-1220',label:'NN14_3-exact-box1220'},
  {file:'primer-probability.html',sha256:'19891bd487ec19b67cbda477809a3a273242c6d4b0647e93c01b94f75108519f',selector:'.definition-box',text:'Conditional expectation and the tower rule',key:'primer-probability.html::node-387',label:'conditional-mean-version387'}
];
const results=[];
const browser=await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM||process.env.HOME+'/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
try{
  for(const t of targets){
    const source=path.join(root,'SafeLearning',t.file);
    if(sha(source)!==t.sha256)throw new Error('ExactSource90 required');
    const page=await browser.newPage({viewport:{width:360,height:900}});
    const runtime=[];
    page.on('pageerror',e=>runtime.push(e.message));
    page.on('console',m=>{if(m.type()==='error')runtime.push(m.text());});
    try{
      await page.goto(pathToFileURL(source).href,{waitUntil:'networkidle'});
      await page.waitForFunction(()=>typeof window.renderMathInElement==='function',null,{timeout:20000});
      const target=page.locator(t.selector).filter({hasText:t.text});
      if(await target.count()!==1)throw new Error('Unique region required');
      await target.evaluate(el=>{for(let n=el;n;n=n.parentElement){if(n.matches('details'))n.open=true;if(n.matches('.collapsible'))n.classList.add('open');}});
      await page.evaluate(()=>document.fonts.ready);
      await settle(page,350);
      const scrolls=await target.evaluate(el=>[...el.querySelectorAll('*')].filter(n=>n.scrollWidth>n.clientWidth+4&&['auto','scroll'].includes(getComputedStyle(n).overflowX)).map(n=>{
        const maximum=n.scrollWidth-n.clientWidth;n.scrollLeft=maximum;
        return {tag:n.tagName,className:n.className,overflowX:getComputedStyle(n).overflowX,clientWidth:n.clientWidth,
                scrollWidth:n.scrollWidth,maximumScrollLeft:maximum,actualScrollLeft:n.scrollLeft,rightEdgeReachable:n.scrollLeft>=maximum-2};
      }));
      if(!scrolls.length||!scrolls.every(r=>r.rightEdgeReachable))throw new Error('Every wide formula must have reachable right edge');
      const pageWidth=await page.evaluate(()=>document.documentElement.scrollWidth);
      if(pageWidth>368)throw new Error('Document overflow at360');
      const capture=path.join(out,'browser34-source90-changed-region-artifacts-v1',t.label+'-360-formula-right.png');
      if(fs.existsSync(capture))throw new Error('Fresh capture required');
      await target.screenshot({path:capture,animations:'disabled',style:'.sidebar-open,.skip-link {visibility:hidden !important;}'});
      if(sha(source)!==t.sha256)throw new Error('Source changed during scroll check');
      results.push({key:t.key,source:ref(source),viewportWidth:360,scrolls,documentWidth:pageWidth,capture:ref(capture),
                    status:runtime.length?'failed':'passed',runtimeErrors:runtime,visualInspection:'pending'});
    }finally{await page.close();}
  }
}finally{await browser.close();}
const passed=results.length===2&&results.every(r=>r.status==='passed');
fs.writeFileSync(report,JSON.stringify({status:passed?'passed':'failed',results,helper:ref(path.join(out,'source90_mobile_formula_scroll34_v1.mjs')),
  source_bytes_preserved:true,visualInspection:'pending',coverage_complete:false},null,2)+'\n',{flag:'wx'});
console.log(JSON.stringify({report:ref(report),status:passed?'passed':'failed'}));
if(!passed)process.exitCode=1;
