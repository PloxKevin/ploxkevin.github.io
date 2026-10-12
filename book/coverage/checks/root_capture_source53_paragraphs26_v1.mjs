// Capture the three changed prose locations for an explicit visual review.
import {chromium} from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import {pathToFileURL} from 'node:url';

const root = process.cwd();
const file = path.join(root, 'reports/full-coverage/browser-input26-source53/SafeLearning/lyapunov-mpc.html');
const output = path.join(root, 'reports/full-coverage/source53-paragraph-screenshots26-v1.json');
const artifacts = path.join(root, 'reports/full-coverage/source53-paragraph-screenshots26-v1');
const hash = filename => crypto.createHash('sha256').update(fs.readFileSync(filename)).digest('hex');
const expected = '5e21c5319d41968468781ee0bf9b18aec5147666f764827f3a96e9e73d0138af';
if (fs.existsSync(output) || fs.existsSync(artifacts)) throw new Error('New output paths required');
if (hash(file) !== expected || hash(path.join(root, 'SafeLearning/lyapunov-mpc.html')) !== expected)
  throw new Error('Source53 snapshot mismatch');
fs.mkdirSync(artifacts);
const browser = await chromium.launch({executablePath:process.env.SAFELEARNING_CHROMIUM ||
  process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'});
const captures = [];
try {
  for (const [name, width, height] of [['desktop', 1280, 900], ['mobile', 375, 812]]) {
    const page = await browser.newPage({viewport:{width,height}});
    await page.goto(pathToFileURL(file).href, {waitUntil:'networkidle'});
    await page.waitForFunction(() => typeof window.renderMathInElement === 'function');
    await page.evaluate(() => {
      document.querySelectorAll('details').forEach(node => node.open = true);
      document.querySelectorAll('.collapsible').forEach(node => node.classList.add('open'));
      window.renderMathInElement(document.body, {delimiters:[
        {left:'$$',right:'$$',display:true},{left:'$',right:'$',display:false},
        {left:'\\(',right:'\\)',display:false},{left:'\\[',right:'\\]',display:true}],throwOnError:false});
    });
    await page.evaluate(() => document.fonts.ready);
    const locations = [
      ['robust-mpc-validation', page.locator('.definition-box').filter({has:page.locator('.box-label',
        {hasText:'Robust MPC and its learned approximation'})})],
      ['scenario-uniqueness', page.locator('.definition-box').filter({has:page.locator('.box-label',
        {hasText:'The scenario approach'})})],
      ['finite-entry-answer', page.locator('p').filter({hasText:'With probability at least'}).filter({hasText:'at every step before entry'})]
    ];
    for (const [location, locator] of locations) {
      if (await locator.count() !== 1) throw new Error('Ambiguous location: ' + location);
      const text = await locator.textContent();
      if (await locator.locator('.katex-error').count()) throw new Error('Math rendering error: ' + location);
      const target = path.join(artifacts, name + '-' + location + '.png');
      await locator.screenshot({path:target,animations:'disabled'});
      const box = await locator.boundingBox();
      captures.push({viewport:{name,width,height},location,path:path.relative(root,target),
        sha256:hash(target),bytes:fs.statSync(target).size,bounding_box:box,
        rendered_text_sha256:crypto.createHash('sha256').update(text).digest('hex')});
    }
    await page.close();
  }
} finally {
  await browser.close();
}
if (captures.length !== 6 || hash(file) !== expected) throw new Error('Capture/source integrity failure');
fs.writeFileSync(output, JSON.stringify({status:'passed_actual_capture_manual_visual_review_pending',
  captured_at_utc:new Date().toISOString(),source_sha256:expected,captures,
  scope:'Six actual desktop/mobile captures of three changed prose locations. This capture record does not claim visual inspection or whole-site manual screenshot review.'},null,2)+'\n',{flag:'wx'});
process.stdout.write(JSON.stringify({status:'passed_actual_capture',captures:captures.length})+'\n');
