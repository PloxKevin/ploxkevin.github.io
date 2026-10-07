// Whole-site reader QA. Run from repository root; default: every SafeLearning HTML page.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

const args = process.argv.slice(2);
const flag = args.indexOf('--report');
const reportPath = flag < 0 ? 'reports/learning-review/browser-final.json' : args.splice(flag, 2)[1];
const site = path.resolve(process.env.SAFELEARNING_QA_SITE || 'SafeLearning');
const files = args.length ? args : fs.readdirSync(site).filter(f => f.endsWith('.html')).sort();
const browser = await chromium.launch({
  executablePath: process.env.SAFELEARNING_CHROMIUM || process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'
});
const report = [];
const leftover = root => {
  const out = [];
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
  while (walker.nextNode()) {
    const node = walker.currentNode;
    if (!node.parentElement.closest('script,style,textarea,.katex') && node.nodeValue.includes('$'))
      out.push(node.nodeValue.trim().slice(0, 150));
  }
  return out;
};

for (const name of files) {
  const file = path.join(site, name);
  const fingerprint = () => crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
  const r = { file: name, source_sha256: fingerprint(), errors: [], exerciseCounts: {}, viewports: [] };
  const page = await browser.newPage({viewport:{width:1280,height:900}});
  page.on('pageerror', e => r.errors.push('Runtime: ' + e.message));
  page.on('console', m => { if (m.type() === 'error') r.errors.push('Console: ' + m.text()); });
  await page.goto('file://' + file, {waitUntil:'networkidle'});
  if (fs.readFileSync(file,'utf8').includes('katex.min.js')) {
    await page.waitForFunction(() => typeof window.renderMathInElement === 'function',null,{timeout:20000})
      .catch(() => r.errors.push('KaTeX did not load'));
  }
  const links = await page.locator('a[href]').evaluateAll(els => els.map(e => e.getAttribute('href')));
  for (const href of new Set(links)) {
    if (/^(https?:|mailto:|javascript:)/.test(href)) continue;
    const [filename, rawAnchor] = href.split('#');
    const target = path.resolve(site, filename || name);
    if (!fs.existsSync(target)) {r.errors.push('Missing file: ' + href); continue;}
    if (rawAnchor) {
      const anchor = decodeURIComponent(rawAnchor);
      const dynamic = !filename || filename === name;
      const exists = dynamic
        ? await page.evaluate(id => !!document.getElementById(id), anchor)
        : new Set([...fs.readFileSync(target,'utf8').matchAll(/\bid=["']([^"']+)["']/g)].map(m => m[1])).has(anchor);
      if (!exists) r.errors.push('Missing anchor: ' + href);
    }
  }
  const structure = await page.evaluate(() => {
    const exercises = [...document.querySelectorAll('details')].filter(d => /^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)/i.test(d.querySelector(':scope > summary')?.textContent.trim() || ''));
    const levelOf = text => {
      const m = text.trim().match(/^(Easy|Medium|Hard)\s+\d+\b|[—–-]\s*(Easy|Medium|Hard)\s*:/i);
      const level = m && (m[1] || m[2]);
      return level ? level[0].toUpperCase()+level.slice(1).toLowerCase() : null;
    };
    const graded = exercises.filter(d => levelOf(d.querySelector(':scope > summary').textContent));
    const counts = {total: exercises.length};
    const issues = [];
    for (const level of ['Easy','Medium','Hard'])
      counts[level] = graded.filter(d => levelOf(d.querySelector(':scope > summary').textContent)===level).length;
    for (const d of graded) {
      const nested = [...d.querySelectorAll('details > summary')].map(s => s.textContent.trim());
      if (!nested.some(s => /hint/i.test(s)) || !nested.some(s => /answer|solution/i.test(s)))
        issues.push('Missing separate hint/solution: ' + d.querySelector(':scope > summary').textContent.trim());
    }
    const ids = [...document.querySelectorAll('[id]')].map(e => e.id);
    const duplicates = ids.filter((id,i) => ids.indexOf(id) !== i);
    const coverage = [];
    for (const h of document.querySelectorAll('h2')) {
      if (!/^\d+\.\s/.test(h.textContent.trim()) || /Walkthrough|Interactive/.test(h.textContent)) continue;
      const text = [];
      for (let el=h.nextElementSibling;el && el.tagName!=='H2';el=el.nextElementSibling)
        text.push(...[...el.querySelectorAll('summary')].map(s => s.textContent));
      coverage.push({id:h.id,levels:['Easy','Medium','Hard'].filter(level => text.some(t => levelOf(t)===level))});
    }
    return {counts,issues,duplicates,coverage};
  });
  r.exerciseCounts = structure.counts;
  if (name.startsWith('primer-')) {
    r.sectionPractice=structure.coverage;
    for (const section of structure.coverage)
      if (section.levels.length!==3) r.errors.push('Missing graded section practice: ' + section.id);
  }
  r.errors.push(...structure.issues,...structure.duplicates.map(id => 'Duplicate ID: ' + id));
  const teachingPage = !['index.html','study-guide.html','formulas.html','papers.html','open-problems.html'].includes(name);
  if (teachingPage && !await page.locator('#reading-route').count()) r.errors.push('Missing first-reading route');
  if (teachingPage && !name.startsWith('primer-')) {
    if (!await page.locator('#graded-practice').count()) r.errors.push('Missing graded practice');
    for (const level of ['Easy','Medium','Hard']) if (r.exerciseCounts[level] < 4) r.errors.push('Too few ' + level + ' problems');
  }
  if (await page.locator('.collapsible-header').count()) {
    const header = page.locator('.collapsible-header').first();
    const before = await header.getAttribute('aria-expanded');
    await header.focus();
    await page.keyboard.press('Enter');
    if (await header.getAttribute('aria-expanded') === before) r.errors.push('Enter did not toggle proof');
    await page.keyboard.press('Space');
    if (await header.getAttribute('aria-expanded') !== before) r.errors.push('Space did not toggle proof');
  }
  const dynamicErrors = await page.evaluate(source => {
    const lo = eval('(' + source + ')');
    const found = [];
    document.querySelectorAll('*').forEach(el => {
      if (el._walkthrough) {
        const n = el.querySelectorAll('.walkthrough-step-tab').length;
        for (let i=0;i<n;i++) {
          el._walkthrough.goTo(i);
          found.push(...lo(el));
          if ([...el.querySelectorAll('.walkthrough-step-tab')].some(tab => tab.tagName !== 'BUTTON'))
            found.push('Walkthrough steps must be buttons');
        }
        el._walkthrough.goTo(0);
      }
      if (el._state?.cards) {
        for (let i=0;i<el._state.cards.length;i++) {
          el._state.setIndex(i); el._state.reveal(); el._state.render();
          found.push(...lo(el));
        }
        el._state.setIndex(0); el._state.render();
      }
    });
    return found;
  }, leftover.toString());
  r.errors.push(...dynamicErrors.map(s => 'Dynamic math: ' + s));
  const sliders = await page.locator('input[type=range]').count();
  r.sliderCount = sliders;
  for (let i=0;i<sliders;i++) await page.locator('input[type=range]').nth(i).evaluate(el => {
    const initial = el.value;
    for (const value of [el.min || '0',el.max || '100',initial]) {
      el.value=value;
      el.dispatchEvent(new Event('input',{bubbles:true}));
      el.dispatchEvent(new Event('change',{bubbles:true}));
    }
  });
  r.errors.push(...(await page.evaluate(leftover,await page.locator('body').elementHandle())).map(s => 'Unrendered math: ' + s));
  r.errors.push(...await page.locator('.katex-error').evaluateAll(els => els.map(e => 'KaTeX: ' + (e.title || e.textContent))));
  for (const width of [320,390,768,820,1280]) {
    await page.setViewportSize({width,height:900});
    await page.evaluate(() => {
      document.querySelectorAll('.collapsible').forEach(c => c.classList.add('open'));
      document.querySelectorAll('details').forEach(d => d.open=true);
    });
    await page.waitForTimeout(350);
    const v = await page.evaluate(() => ({
      width:innerWidth,
      documentWidth:document.documentElement.scrollWidth,
      clipped:[...document.querySelectorAll('.collapsible-body,details')].filter(e => e.scrollWidth>e.clientWidth+4)
        .map(e => ({label:(e.closest('.collapsible,details').querySelector('.collapsible-header,summary')?.textContent || '').trim().slice(0,100),width:e.clientWidth,scrollWidth:e.scrollWidth}))
    }));
    r.viewports.push(v);
    if (v.documentWidth>width+8) r.errors.push('Page overflow at ' + width + ': ' + v.documentWidth);
    if (v.clipped.length) r.errors.push('Clipped expanded boxes at ' + width + ': ' + JSON.stringify(v.clipped));
    if (width===390 && await page.locator('.sidebar-open').count()) {
      await page.locator('.sidebar-open').click();
      await page.waitForTimeout(350);
      const open = await page.locator('#sidebar').evaluate(e => e.classList.contains('open-mobile') && e.getBoundingClientRect().left>=-1);
      if (!open) r.errors.push('Mobile navigation did not open');
      await page.locator('.sidebar-toggle').click();
      if (await page.locator('#sidebar').evaluate(e => e.classList.contains('open-mobile'))) r.errors.push('Mobile navigation did not close');
    }
  }
  await page.close();
  if (fingerprint() !== r.source_sha256) r.errors.push('Source changed during browser verification');
  r.errors = [...new Set(r.errors)];
  report.push(r);
  fs.mkdirSync(path.dirname(reportPath),{recursive:true});
  fs.writeFileSync(reportPath,JSON.stringify(report,null,2));
  console.log(name + ': ' + r.exerciseCounts.total + ' exercises; ' + r.errors.length + ' issues');
  if (r.errors.length) console.log(JSON.stringify(r.errors));
}
await browser.close();
if (report.some(r => r.errors.length)) process.exitCode=1;
