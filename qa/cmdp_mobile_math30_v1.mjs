// Check actual horizontal mouse-wheel access to the qualified CMDP formulas.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';

const destination = 'reports/full-coverage/cmdp-mobile-math30-v1.json';
if (fs.existsSync(destination)) throw new Error('Use a fresh output path');
const sources = ['SafeLearning/cmdp.html', 'SafeLearning/style.css', 'qa/cmdp_mobile_math30_v1.mjs'];
const sha = n => crypto.createHash('sha256').update(fs.readFileSync(n)).digest('hex');
const before = Object.fromEntries(sources.map(n => [n, sha(n)]));
const start = performance.now();
const report = { status: 'running', started_at_utc: new Date().toISOString(), source_sha256: before, viewports: [], errors: [] };
const browser = await chromium.launch({ executablePath: process.env.SAFELEARNING_CHROMIUM || process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell' });
try {
  for (const width of [320, 360, 390, 1280]) {
    const page = await browser.newPage({ viewport: { width, height: 900 } });
    try {
      await page.goto(pathToFileURL(path.resolve('SafeLearning/cmdp.html')).href, { waitUntil: 'networkidle' });
      await page.evaluate(() => {
        document.querySelectorAll('.collapsible').forEach(n => n.classList.add('open'));
        document.querySelectorAll('details').forEach(n => { n.open = true; });
      });
      await page.waitForTimeout(500);
      const geometry = await page.evaluate(() => ({ width: innerWidth, document_width: document.documentElement.scrollWidth }));
      const row = { ...geometry, formulas: [] }; report.viewports.push(row);
      if (geometry.document_width > width + 1) throw new Error('Page overflow at ' + width);
      const box = page.locator('.definition-box').filter({ hasText: 'State-augmented CRL produces feasible, near-optimal trajectories' });
      for (const prefix of ['\\liminf_{N\\to\\infty}', '\\liminf_{T\\to\\infty}']) {
        const candidates = box.locator('.katex'); let formula = null;
        for (let i = 0; i < await candidates.count(); i++) {
          const candidate = candidates.nth(i);
          if ((await candidate.locator('annotation').textContent()).startsWith(prefix)) { formula = candidate; break; }
        }
        if (!formula) throw new Error('Missing exact average-guarantee formula');
        const record = { tex: await formula.locator('annotation').textContent() }; row.formulas.push(record);
        await formula.scrollIntoViewIfNeeded();
        record.before = await formula.evaluate(n => ({ client_width: n.clientWidth, scroll_width: n.scrollWidth, scroll_left: n.scrollLeft, overflow_x: getComputedStyle(n).overflowX }));
        if (width <= 360) {
          if (record.before.overflow_x !== 'auto' || record.before.scroll_width <= record.before.client_width + 4) throw new Error('Expected bounded scroll container');
          const rect = await formula.boundingBox();
          await page.mouse.move(rect.x + Math.min(rect.width - 2, rect.width / 2), rect.y + rect.height / 2);
          await page.mouse.wheel(5000, 0); await page.waitForTimeout(250);
          record.right = await formula.evaluate(n => n.scrollLeft);
          if (Math.abs(record.right - (record.before.scroll_width - record.before.client_width)) > 2) throw new Error('Right end is inaccessible');
          await page.mouse.wheel(-5000, 0); await page.waitForTimeout(250);
          record.left = await formula.evaluate(n => n.scrollLeft);
          if (record.left > 1) throw new Error('Left end is inaccessible');
        }
        record.passed = true;
      }
      row.passed = true;
    } finally { await page.close(); }
  }
} catch (error) { report.errors.push(String(error)); }
finally { await browser.close(); }
report.source_sha256_after = Object.fromEntries(sources.map(n => [n, sha(n)]));
if (JSON.stringify(before) !== JSON.stringify(report.source_sha256_after)) report.errors.push('Source changed during check');
report.finished_at_utc = new Date().toISOString(); report.elapsed_seconds = (performance.now() - start) / 1000;
report.status = report.errors.length ? 'failed' : 'passed_actual_CMDP_mobile_width_and_both_formula_mouse_wheel_endpoints';
report.scope = 'The two exact qualified epoch/all-time objective formulas at four widths; actual wheel endpoints at 320 and 360. This is not a whole-page visual review.';
fs.writeFileSync(destination, JSON.stringify(report, null, 2) + '\n', { flag: 'wx' });
console.log(JSON.stringify({ status: report.status, viewports: report.viewports.length, errors: report.errors }));
if (report.errors.length) process.exitCode = 1;
