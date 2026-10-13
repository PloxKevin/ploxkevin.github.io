import { chromium } from '/home/oxrexkevin/SafetyBased/qa/node_modules/playwright-core/index.mjs';
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const ROOT = '/home/oxrexkevin/SafetyBased';
const FOLDER = path.join(ROOT, 'book/solutions/drafts');
const CANDIDATE = 'book/solutions/drafts/primer-basics-validation-v1/SafeLearning/primer-basics.html';
const SOURCE = 'SafeLearning/primer-basics.html';
const REPORT = 'book/solutions/drafts/primer-basics-rendered-draft-v1.json';
const digest = file => crypto.createHash('sha256').update(fs.readFileSync(path.join(ROOT, file))).digest('hex');
const ref = file => ({ file, sha256: digest(file) });
const protectedFiles = [SOURCE, 'book/chapters/primer-basics.html', 'SafeLearning/style.css',
  'SafeLearning/components.js', 'book/solutions/drafts/primer-basics-thorough-solutions-v1.json'];
const before = Object.fromEntries(protectedFiles.map(f => [f, digest(f)]));
const mime = { '.html': 'text/html; charset=utf-8', '.js': 'text/javascript', '.css': 'text/css',
  '.png': 'image/png', '.svg': 'image/svg+xml', '.woff2': 'font/woff2' };
const server = http.createServer((req, res) => {
  const name = decodeURIComponent(new URL(req.url, 'http://127.0.0.1').pathname);
  if (name === '/favicon.ico') { res.writeHead(204); res.end(); return; }
  const file = name === '/' + SOURCE ? path.join(ROOT, CANDIDATE) : path.resolve(ROOT, '.' + name);
  if (!file.startsWith(ROOT + '/') || !fs.existsSync(file) || !fs.statSync(file).isFile()) {
    res.writeHead(404); res.end(); return;
  }
  res.writeHead(200, { 'Content-Type': mime[path.extname(file)] || 'application/octet-stream' });
  res.end(fs.readFileSync(file));
});
await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
const address = server.address();
const browser = await chromium.launch({
  executablePath: '/home/oxrexkevin/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'
});
const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
const consoleErrors = [], pageErrors = [];
page.on('console', m => { if (['error', 'warning'].includes(m.type())) consoleErrors.push(m.text()); });
page.on('pageerror', e => pageErrors.push(String(e)));
const widths = [];
const screenshots = [];
try {
  await page.goto('http://127.0.0.1:' + address.port + '/' + SOURCE, { waitUntil: 'networkidle' });
  await page.waitForFunction(() => typeof window.renderMathInElement === 'function', null, { timeout: 30000 });
  await page.evaluate(() => {
    document.querySelectorAll('details').forEach(d => { d.open = true; });
    document.querySelectorAll('.collapsible').forEach(d => d.classList.add('open'));
  });
  await page.waitForTimeout(600);
  const staticChecks = await page.evaluate(() => {
    const leftovers = [];
    const walker = document.createTreeWalker(document.body, NodeFilter.SHOW_TEXT);
    while (walker.nextNode()) {
      const n = walker.currentNode;
      if (n.parentElement?.closest('script,style,textarea,.katex')) continue;
      if (n.nodeValue.includes('$')) leftovers.push(n.nodeValue.trim().slice(0, 160));
    }
    const exercises = [...document.querySelectorAll('details')]
      .filter(d => /^Exercise\b/.test(d.querySelector(':scope > summary')?.textContent.trim() || ''));
    const missingAnchors = [...document.querySelectorAll('a[href^="#"]')].map(a => a.getAttribute('href').slice(1))
      .filter(id => id && !document.getElementById(id));
    const crossLinks = [...document.querySelectorAll('a[href]')].map(a => a.getAttribute('href'))
      .filter(h => !/^(https?:|mailto:|#)/.test(h));
    return { exerciseCount: exercises.length, leftoverDollar: leftovers,
      katexErrors: [...document.querySelectorAll('.katex-error')].map(e => e.getAttribute('title') || e.textContent),
      missingAnchors, crossLinks,
      explorer: { cobwebElements: document.querySelector('#p0-cob')?.childElementCount,
        errorElements: document.querySelector('#p0-err')?.childElementCount,
        geometricElements: document.querySelector('#p0-geo')?.childElementCount } };
  });
  const brokenLinks = [];
  for (const href of staticChecks.crossLinks) {
    const [file, anchor] = href.split('#');
    const target = path.resolve(ROOT, 'SafeLearning', file);
    if (!fs.existsSync(target) || (anchor && !fs.readFileSync(target, 'utf8').includes('id="' + anchor + '"')))
      brokenLinks.push(href);
  }
  for (const width of [1280, 390, 320]) {
    await page.setViewportSize({ width, height: 900 });
    await page.waitForTimeout(450);
    const measure = await page.evaluate(() => {
      const clipped = [];
      for (const d of document.querySelectorAll('details,.collapsible-body')) {
        if (d.scrollWidth > d.clientWidth + 4)
          clipped.push({ title: d.querySelector('summary')?.textContent.trim().replace(/\s+/g, ' '),
            scrollWidth: d.scrollWidth, clientWidth: d.clientWidth });
      }
      return { viewport: innerWidth, pageScrollWidth: document.documentElement.scrollWidth,
        mobileOverflow: document.documentElement.scrollWidth > innerWidth + 8, clippedExpandedDisclosures: clipped };
    });
    widths.push({ width, ...measure });
  }
  await page.setViewportSize({ width: 390, height: 900 });
  const mixed = page.locator('details').filter({ has: page.locator(':scope > summary', { hasText: "Exercise 0.6 — Reading rates and costs" }) });
  if (await mixed.count() === 1) {
    const file = 'book/solutions/drafts/primer-basics-rates-mobile-v1.png';
    await mixed.screenshot({ path: path.join(ROOT, file), timeout: 30000 });
    screenshots.push(ref(file));
  }
  await page.setViewportSize({ width: 1280, height: 900 });
  const explorerShot = 'book/solutions/drafts/primer-basics-explorer-desktop-v1.png';
  await page.locator('#p0-cob').screenshot({ path: path.join(ROOT, explorerShot) });
  screenshots.push(ref(explorerShot));
  const errors = [
    ...consoleErrors.map(e => 'console: ' + e), ...pageErrors.map(e => 'page: ' + e),
    ...staticChecks.katexErrors.map(e => 'katex: ' + e), ...staticChecks.leftoverDollar.map(e => 'leftover math: ' + e),
    ...staticChecks.missingAnchors.map(e => 'missing anchor: ' + e), ...brokenLinks.map(e => 'broken link: ' + e)
  ];
  if (staticChecks.exerciseCount !== 50) errors.push('Expected exactly 50 exercises');
  for (const m of widths) {
    if (m.mobileOverflow) errors.push('Page overflow at width ' + m.width);
    for (const d of m.clippedExpandedDisclosures) errors.push('Expanded disclosure clipped at ' + m.width + ': ' + d.title);
  }
  if (!Object.values(staticChecks.explorer).every(n => n > 0)) errors.push('An existing explorer did not render');
  for (const file of protectedFiles) if (digest(file) !== before[file]) errors.push('Protected input changed: ' + file);
  const result = {
    status: errors.length ? 'failed_rendered_draft_checks' : 'passed_rendered_draft_checks',
    candidate: ref(CANDIDATE), draft: ref('book/solutions/drafts/primer-basics-thorough-solutions-v1.json'),
    checker: ref('book/solutions/drafts/check_primer_basics_draft_v1.mjs'),
    browserVersion: browser.version(), checkedAtUtc: new Date().toISOString(),
    consoleErrors, pageErrors, ...staticChecks, brokenLinks, widths, screenshots, errors,
    protectedInputsBefore: before, protectedInputsAfter: Object.fromEntries(protectedFiles.map(f => [f, digest(f)])),
    canonicalSourcesModified: false, independentPedagogicalReviewPending: true
  };
  fs.writeFileSync(path.join(ROOT, REPORT), JSON.stringify(result, null, 2) + '\n');
  console.log(JSON.stringify({ status: result.status, report: ref(REPORT), errors, widths, screenshots }));
} finally {
  await page.close();
  await browser.close();
  await new Promise(resolve => server.close(resolve));
}
