import { chromium } from '/home/oxrexkevin/SafetyBased/qa/node_modules/playwright-core/index.mjs';
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { fileURLToPath } from 'node:url';

const SELF = fileURLToPath(import.meta.url);
const ROOT = path.resolve(path.dirname(SELF), '../..');
const REPORT = 'reports/solution-review/peer-three-page-render-v2.json';
const targets = [
  { page: 'primer-rl-nn.html', count: 42, version: 'v2', draft: 'book/solutions/drafts/primer-rl-nn-thorough-solutions-v2.json',
    candidate: 'book/solutions/candidates/primer-rl-nn-v2/SafeLearning/primer-rl-nn.html' },
  { page: 'cmdp.html', count: 21, version: 'v1', draft: 'book/solutions/drafts/cmdp-thorough-solutions-v1.json',
    candidate: 'book/solutions/candidates/cmdp-v1/SafeLearning/cmdp.html' },
  { page: 'policy-optimization.html', count: 21, version: 'v1', draft: 'book/solutions/drafts/policy-optimization-thorough-solutions-v1.json',
    candidate: 'book/solutions/candidates/policy-optimization-v1/SafeLearning/policy-optimization.html' }
];
const hash = file => crypto.createHash('sha256').update(fs.readFileSync(path.join(ROOT, file))).digest('hex');
const ref = file => ({ file, sha256: hash(file) });
const protectedFiles = [
  path.relative(ROOT, SELF), 'SafeLearning/style.css', 'SafeLearning/components.js',
  ...targets.flatMap(t => [t.draft, t.candidate])
];
const before = protectedFiles.map(ref);
const mime = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css',
  '.svg': 'image/svg+xml', '.png': 'image/png', '.woff2': 'font/woff2' };
const server = http.createServer((req, res) => {
  const pathname = decodeURIComponent(new URL(req.url, 'http://127.0.0.1').pathname);
  if (pathname === '/favicon.ico') { res.writeHead(204); res.end(); return; }
  const target = targets.find(t => pathname === '/SafeLearning/' + t.page);
  const local = target ? path.join(ROOT, target.candidate) : path.resolve(ROOT, '.' + pathname);
  if (!local.startsWith(ROOT + '/') || !fs.existsSync(local) || !fs.statSync(local).isFile()) {
    res.writeHead(404); res.end(); return;
  }
  res.writeHead(200, { 'Content-Type': mime[path.extname(local)] || 'application/octet-stream' });
  res.end(fs.readFileSync(local));
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const port = server.address().port;
const browser = await chromium.launch({
  executablePath: '/home/oxrexkevin/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'
});
const pages = [], errors = [];
try {
  for (const target of targets) {
    const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
    const consoleErrors = [], pageErrors = [];
    page.on('console', m => { if (m.type() === 'error') consoleErrors.push(m.text()); });
    page.on('pageerror', e => pageErrors.push(String(e)));
    const record = { page: target.page, draft: ref(target.draft), candidate: ref(target.candidate),
      consoleErrors, pageErrors, widths: [], screenshots: [], errors: [] };
    try {
      await page.goto('http://127.0.0.1:' + port + '/SafeLearning/' + target.page, { waitUntil: 'networkidle' });
      await page.waitForFunction(() => typeof window.renderMathInElement === 'function', null, { timeout: 30000 });
      await page.evaluate(() => {
        document.querySelectorAll('details').forEach(d => { d.open = true; });
        document.querySelectorAll('.collapsible').forEach(d => d.classList.add('open'));
      });
      const checks = await page.evaluate(() => {
        const leftovers = [];
        const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
        while (walker.nextNode()) {
          const node = walker.currentNode;
          if (node.parentElement?.closest('script,style,textarea,.katex')) continue;
          if (node.nodeValue.includes('$')) leftovers.push(node.nodeValue.trim().slice(0, 160));
        }
        const exercises = [...document.querySelectorAll('details')].filter(d =>
          /^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)/i.test(d.querySelector(':scope > summary')?.textContent.trim() || ''));
        return {
          exerciseCount: exercises.length,
          leftoverDollar: leftovers,
          katexErrors: [...document.querySelectorAll('.katex-error')].map(e => e.title || e.textContent),
          missingAnchors: [...document.querySelectorAll('a[href^="#"]')].map(a => a.getAttribute('href').slice(1))
            .filter(id => id && !document.getElementById(id)),
          crossLinks: [...document.querySelectorAll('a[href]')].map(a => a.getAttribute('href'))
            .filter(h => !/^(https?:|mailto:|#)/.test(h)),
          explorerSvgCount: document.querySelectorAll('.interactive-container svg').length,
          explorerSvgChildren: [...document.querySelectorAll('.interactive-container svg')].map(s => s.childElementCount)
        };
      });
      await page.waitForTimeout(450);
      Object.assign(record, checks);
      record.brokenLinks = [];
      for (const href of checks.crossLinks) {
        const [file, anchor] = href.split('#');
        const local = path.resolve(ROOT, 'SafeLearning', file);
        if (!fs.existsSync(local) || (anchor && !fs.readFileSync(local, 'utf8').includes('id="' + anchor + '"')))
          record.brokenLinks.push(href);
      }
      if (checks.exerciseCount !== target.count) record.errors.push('exercise_count');
      for (const key of ['leftoverDollar', 'katexErrors', 'missingAnchors', 'brokenLinks'])
        for (const value of record[key]) record.errors.push(key + ': ' + value);
      if (!checks.explorerSvgCount || checks.explorerSvgChildren.some(n => n === 0))
        record.errors.push('empty_existing_explorer');

      const slider = page.locator('input[type=range]').first();
      if (await slider.count()) {
        const old = await slider.inputValue();
        await slider.focus();
        await slider.press('ArrowRight');
        if (await slider.inputValue() === old) await slider.press('ArrowLeft');
        record.sliderKeyboardCheck = { before: old, after: await slider.inputValue() };
        if (record.sliderKeyboardCheck.after === old) record.errors.push('slider_keyboard_no_change');
      }
      for (const width of [1280, 390, 320]) {
        await page.setViewportSize({ width, height: 900 });
        await page.waitForTimeout(450);
        const measure = await page.evaluate(() => ({
          viewport: innerWidth, pageScrollWidth: document.documentElement.scrollWidth,
          mobileOverflow: document.documentElement.scrollWidth > innerWidth + 8,
          clippedExpandedDisclosures: [...document.querySelectorAll('details,.collapsible-body')]
            .filter(d => d.scrollWidth > d.clientWidth + 6)
            .map(d => ({ title: d.querySelector('summary')?.textContent.trim().replace(/\s+/g, ' ').slice(0, 140),
              scrollWidth: d.scrollWidth, clientWidth: d.clientWidth }))
        }));
        record.widths.push({ width, ...measure });
        if (measure.mobileOverflow) record.errors.push('page_overflow_at_' + width);
        for (const d of measure.clippedExpandedDisclosures)
          record.errors.push('disclosure_clipped_at_' + width + ': ' + d.title);
      }
      await page.setViewportSize({ width: 1280, height: 900 });
      await page.waitForTimeout(450);
      const shot = 'reports/solution-review/peer-three-page-render-v2-shots/' + target.page.replace('.html', '') + '-explorer.png';
      fs.mkdirSync(path.dirname(path.join(ROOT, shot)), { recursive: true });
      await page.locator('.interactive-container svg').first().screenshot({ path: path.join(ROOT, shot), timeout: 30000 });
      record.screenshots.push(ref(shot));
      for (const e of consoleErrors) record.errors.push('console: ' + e);
      for (const e of pageErrors) record.errors.push('page: ' + e);
    } catch (e) {
      record.errors.push('exception: ' + String(e));
    } finally {
      await page.close();
    }
    record.status = record.errors.length ? 'failed_rendered_candidate_checks' : 'passed_rendered_candidate_checks';
    pages.push(record);
    errors.push(...record.errors.map(e => target.page + ': ' + e));
  }
  const after = protectedFiles.map(ref);
  if (JSON.stringify(before) !== JSON.stringify(after)) errors.push('protected_input_changed');
  const result = {
    status: errors.length ? 'failed_peer_rendered_checks' : 'passed_peer_rendered_checks',
    command: [process.execPath, path.relative(ROOT, SELF)], cwd: ROOT,
    browserVersion: browser.version(), checkedAtUtc: new Date().toISOString(),
    helper: ref(path.relative(ROOT, SELF)), protectedInputsBefore: before, protectedInputsAfter: after,
    pages, errors, checkerWroteCanonicalOrAuthoringSources: false,
    mathematicalAndPedagogicalApprovalClaimed: false
  };
  const fd = fs.openSync(path.join(ROOT, REPORT), 'wx');
  try { fs.writeFileSync(fd, JSON.stringify(result, null, 2) + '\n'); fs.fsyncSync(fd); }
  finally { fs.closeSync(fd); }
  console.log(JSON.stringify({ status: result.status, report: ref(REPORT),
    pageStatuses: pages.map(p => ({page: p.page, status: p.status, errorCount: p.errors.length, firstErrors: p.errors.slice(0, 10)})), errorCount: errors.length, firstErrors: errors.slice(0, 10) }));
  if (errors.length) process.exitCode = 1;
} finally {
  await browser.close();
  await new Promise(resolve => server.close(resolve));
}

