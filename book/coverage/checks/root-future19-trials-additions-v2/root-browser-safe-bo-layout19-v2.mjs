import { createRequire } from 'node:module';
const require=createRequire('/home/oxrexkevin/SafetyBased/qa/learning_review.mjs');
const {chromium}=require('playwright-core');
import fs from 'node:fs';
const browser=await chromium.launch({executablePath:'/home/oxrexkevin/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
const page=await browser.newPage({viewport:{width:1280,height:900}});
await page.goto('file:///home/oxrexkevin/SafetyBased/reports/full-coverage/browser-input-19-source44/SafeLearning/safe-bo-theory.html',{waitUntil:'networkidle'});
const out=[];
for(const width of [320,390,1280,320]) {
 await page.setViewportSize({width,height:900});
 await page.evaluate(()=>{document.querySelectorAll('.collapsible').forEach(e=>e.classList.add('open'));document.querySelectorAll('details').forEach(e=>e.open=true);});
 for(const ms of [350,500,1500]) {await page.waitForTimeout(ms);out.push(await page.evaluate(({ms})=>({ms,width:innerWidth,documentWidth:document.documentElement.scrollWidth,main:[...document.querySelectorAll('main')].map(e=>({rect:e.getBoundingClientRect().toJSON(),marginLeft:getComputedStyle(e).marginLeft,width:getComputedStyle(e).width,display:getComputedStyle(e).display})),match:matchMedia('(max-width:768px)').matches,body:getComputedStyle(document.body).display,clipped:[...document.querySelectorAll('.collapsible-body,details')].filter(e=>e.scrollWidth>e.clientWidth+4).map(e=>({width:e.clientWidth,scroll:e.scrollWidth})).slice(0,4)}),{ms}));}
}
await browser.close();fs.writeFileSync('/home/oxrexkevin/SafetyBased/reports/full-coverage/safe-bo-theory-layout-probe19-v1.json',JSON.stringify(out,null,2));console.log(JSON.stringify(out));
