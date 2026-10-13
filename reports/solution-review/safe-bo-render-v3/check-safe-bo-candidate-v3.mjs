// QA for SafeLearning pages: KaTeX errors, JS errors, unrendered $...$ (static + walkthrough steps + flashcards),
// broken anchors/links, mobile overflow (with cause bisection), full-page screenshots.
// Usage: cd qa && node check.mjs ../SafeLearning/<page>.html [...]   (prints a JSON report)
// (if node itself fails to start, see ~/.local/bin/node and the memory note on the simdjson workaround)
import { chromium } from "file:///home/oxrexkevin/SafetyBased/qa/node_modules/playwright-core/index.mjs";
import fs from 'node:fs';
import path from 'node:path';

const CHROME = process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell';
const SHOTS = "/home/oxrexkevin/SafetyBased/reports/solution-review/safe-bo-render-v3/shots";
fs.mkdirSync(SHOTS, { recursive: true });

const files = process.argv.slice(2).map(f => path.resolve(f));
const browser = await chromium.launch({ executablePath: CHROME });
const report = [];

// Text nodes that still contain "$" after KaTeX ran = math that failed to render.
const LEFTOVER_JS = `(root) => {
  const out = [];
  const w = document.createTreeWalker(root, NodeFilter.SHOW_TEXT, {
    acceptNode(n) {
      const p = n.parentElement;
      if (!p || p.closest('script,style,textarea,.katex')) return NodeFilter.FILTER_REJECT;
      return n.nodeValue.includes('$') ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT;
    }
  });
  while (w.nextNode()) out.push(w.currentNode.nodeValue.trim().slice(0, 120));
  return out;
}`;

for (const file of files) {
  const r = { file: path.basename(file), consoleErrors: [], pageErrors: [], leftoverDollar: [], katexErrors: [],
              missingAnchors: [], brokenLinks: [], mobileOverflow: false };
  const page = await browser.newPage({ viewport: { width: 1280, height: 900 } });
  page.on('console', m => { if (m.type() === 'error' || m.type() === 'warning') r.consoleErrors.push(m.text().slice(0, 300)); });
  page.on('pageerror', e => r.pageErrors.push(String(e).slice(0, 300)));
  await page.goto('file://' + file, { waitUntil: 'networkidle' });
  const usesKatex = fs.readFileSync(file, 'utf8').includes('katex');
  let katexLoaded = false;
  if (usesKatex) {
    katexLoaded = await page.waitForFunction(() => typeof window.renderMathInElement === 'function', null, { timeout: 20000 })
      .then(() => true).catch(() => { r.pageErrors.push('KaTeX never loaded'); return false; });
  }
  if (katexLoaded) {
    // Wait until auto-render has finished: the number of .katex nodes must be stable for 1 s.
    let prev = -1;
    for (let i = 0; i < 30; i++) {
      const n = await page.evaluate(() => document.querySelectorAll('.katex').length);
      if (n === prev && n > 0) break;
      prev = n; await page.waitForTimeout(1000);
    }
  }

  const leftover = new Set(await page.evaluate(`(${LEFTOVER_JS})(document.body)`));

  // Step through every walkthrough and reveal every flashcard so their math renders too.
  const dyn = await page.evaluate(`(() => {
    const found = [];
    const lo = ${LEFTOVER_JS};
    document.querySelectorAll('*').forEach(el => {
      if (el._walkthrough) {
        const n = el.querySelectorAll('.walkthrough-step-tab').length;
        for (let i = 0; i < n; i++) { el._walkthrough.goTo(i); lo(el).forEach(s => found.push('[walkthrough ' + el.id + ' step ' + (i+1) + '] ' + s)); }
        el._walkthrough.goTo(0);
      }
      if (el._state && el._state.cards) {
        const s = el._state;
        for (let i = 0; i < s.cards.length; i++) { s.setIndex(i); s.reveal(); s.render(); lo(el).forEach(t => found.push('[flashcard ' + (i+1) + '] ' + t)); }
        s.setIndex(0); s.render();
      }
    });
    return found;
  })()`);
  dyn.forEach(s => leftover.add(s));
  r.leftoverDollar = [...leftover].slice(0, 25);
  r.katexErrors = await page.evaluate(() => [...document.querySelectorAll('.katex-error')].map(e => (e.getAttribute('title') || e.textContent).slice(0, 120)));

  // In-page anchors used by sidebar + TOC.
  r.missingAnchors = await page.evaluate(() => [...document.querySelectorAll('a[href^="#"]')]
    .map(a => a.getAttribute('href').slice(1)).filter(id => id && !document.getElementById(id)));

  // Cross-page links inside the section: file must exist, anchor must exist in it.
  const links = await page.evaluate(() => [...document.querySelectorAll('a[href]')].map(a => a.getAttribute('href'))
    .filter(h => !/^(https?:|mailto:|#)/.test(h)));
  for (const h of links) {
    const [f, anchor] = h.split('#');
    const target = path.resolve(path.dirname(file), f);
    if (!fs.existsSync(target)) { r.brokenLinks.push(h); continue; }
    if (anchor && !fs.readFileSync(target, 'utf8').includes(`id="${anchor}"`)) r.brokenLinks.push(h);
  }

  // Full-page shots of very long pages can time out; fall back to the viewport.
  const shot = path.join(SHOTS, r.file.replace('.html', '.png'));
  try { await page.screenshot({ path: shot, fullPage: true, timeout: 20000 }); }
  catch (e) { await page.screenshot({ path: shot, fullPage: false }).catch(() => {}); r.screenshotNote = 'full-page screenshot timed out; viewport only'; }

  await page.setViewportSize({ width: 390, height: 844 });
  await page.waitForTimeout(800);
  r.mobileOverflow = await page.evaluate(() => document.documentElement.scrollWidth > window.innerWidth + 8);
  if (r.mobileOverflow) { await page.waitForTimeout(700); r.mobileOverflow = await page.evaluate(() => document.documentElement.scrollWidth > window.innerWidth + 8); }
  if (r.mobileOverflow) {
    // Bisect: which element groups / top-level blocks widen the page at 390px?
    r.mobileOverflowCause = await page.evaluate(() => {
      const sw = () => document.documentElement.scrollWidth, base = sw(), out = { scrollWidth: base, groups: [], blocks: [] };
      for (const sel of ['.sidebar', 'table', '.katex-display', '.katex', 'svg', '.algorithm', '.interactive-container', '.walkthrough-content', '.flashcard', 'details', 'pre', 'img']) {
        const els = [...document.querySelectorAll(sel)], prev = els.map(e => e.style.display);
        els.forEach(e => e.style.display = 'none');
        if (sw() < base) out.groups.push(sel + ' -> ' + sw());
        els.forEach((e, i) => e.style.display = prev[i]);
      }
      for (const s of document.querySelectorAll('.main-content > *')) {
        const d = s.style.display; s.style.display = 'none'; const v = sw(); s.style.display = d;
        if (v < base) out.blocks.push((s.tagName + '#' + s.id + '.' + String(s.className).split(' ')[0] + ' "' + (s.textContent || '').trim().slice(0, 40) + '"') + ' -> ' + v);
      }
      return out;
    });
  }
  // Collapsed boxes (worked examples, proofs, answers) hide their content from the check above. Boxes clip
  // (overflow: hidden), so too-wide content inside them is cut off rather than widening the page: open every box
  // at 390px and report each one whose content is wider than the box itself.
  r.mobileOverflowExpanded = await page.evaluate(async () => {
    document.querySelectorAll('.collapsible').forEach(c => c.classList.add('open'));
    document.querySelectorAll('details').forEach(d => { d.open = true; });
    await new Promise(res => setTimeout(res, 400));
    const out = [];
    if (document.documentElement.scrollWidth > window.innerWidth + 8) out.push('(page wider than the viewport)');
    for (const b of document.querySelectorAll('.collapsible-body, details')) {
      if (b.scrollWidth > b.clientWidth + 4) {
        const box = b.closest('.collapsible, details');
        out.push((box.querySelector('.collapsible-header, summary')?.textContent || '').trim().replace(/\s+/g, ' ').slice(0, 80) + ` (${b.scrollWidth}px > ${b.clientWidth}px)`);
      }
    }
    return out;
  });
  await page.close();
  report.push(r);
}

await browser.close();
console.log(JSON.stringify(report, null, 2));
