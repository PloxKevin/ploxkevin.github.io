import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { settle } from '../../../qa/book_browser_checks.mjs';

const root = process.cwd();
const source = 'reports/full-coverage/browser-input24-source52/SafeLearning/nn-in-the-loop.html';
const expected = '1a39cab6587a6fe91dca670facc5e58e7c85cb6c0a2c065f43763656d5b73041';
const output = 'reports/full-coverage/source52-corrected-paragraphs24-capture-v1.json';
const directory = 'reports/full-coverage/source52-corrected-paragraphs24-captures-v1';
const digest = file => crypto.createHash('sha256').update(fs.readFileSync(path.join(root,file))).digest('hex');
if (digest(source) !== expected || fs.existsSync(output) || fs.existsSync(directory)) throw new Error('Source or new-output precondition failed');
fs.mkdirSync(directory);
const browser = await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM || process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
const started = new Date().toISOString();
const captures = [];
try {
  for (const width of [390,1280]) {
    const page = await browser.newPage({viewport:{width,height:900}});
    const errors = [];
    page.on('pageerror', e => errors.push(String(e)));
    page.on('console', m => { if (m.type() === 'error') errors.push(m.text()); });
    await page.goto(pathToFileURL(path.join(root,source)).href,{waitUntil:'networkidle'});
    await page.waitForFunction(() => typeof window.renderMathInElement === 'function');
    for (const [label,text] of [
      ['answer-b','A certificate that requires this QC for all shifted inputs'],
      ['answer-c','The ordinary monotone Zames']
    ]) {
      const paragraph = page.locator('p').filter({hasText:text});
      if (await paragraph.count() !== 1) throw new Error('Target paragraph must be unique');
      await paragraph.evaluate(node => {
        let parent = node.parentElement;
        while (parent) { if (parent.tagName === 'DETAILS') parent.open = true; parent = parent.parentElement; }
      });
      await settle(page,300);
      if (await paragraph.locator('.katex-error').count()) throw new Error('Target math parse error');
      if (await paragraph.locator('.katex').count() === 0) throw new Error('Target math did not render');
      const file = `${directory}/${label}-${width}.png`;
      await paragraph.screenshot({path:path.join(root,file)});
      captures.push({label,width,file,sha256:digest(file),source_sha256:expected,
        actual_rendered_math_count:await paragraph.locator('.katex').count(),
        scope:'Actual corrected paragraph capture. Manual visual review remains separate.'});
    }
    if (errors.length) throw new Error(JSON.stringify(errors));
    await page.close();
  }
} finally { await browser.close(); }
if (digest(source) !== expected || captures.length !== 4) throw new Error('Postcondition failed');
fs.writeFileSync(output,JSON.stringify({status:'passed_actual_four_corrected_paragraph_captures',
  started_at_utc:started,finished_at_utc:new Date().toISOString(),actual_workdir:root,
  source,source_sha256:expected,captures,manual_visual_review:'pending',coverage_complete:false},null,2)+'\n');
console.log(JSON.stringify({status:'passed_actual_capture',captures:captures.length,manual_visual_review:'pending'}));
