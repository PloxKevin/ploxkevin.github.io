// Reader checks shared by the whole-site QA runner. These require a running browser.
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';

export async function settle(page, delay = 60) {
  await page.evaluate(() => new Promise(resolve => requestAnimationFrame(() => requestAnimationFrame(resolve))));
  await page.waitForTimeout(delay);
}

export function renderedMathProblems(root) {
  const problems = [];
  const walker = document.createTreeWalker(root, NodeFilter.SHOW_TEXT);
  while (walker.nextNode()) {
    const node = walker.currentNode;
    if (!node.parentElement.closest('script,style,textarea,.katex') && node.nodeValue.includes('$'))
      problems.push('Unrendered math: ' + node.nodeValue.trim().slice(0, 150));
  }
  problems.push(...[...root.querySelectorAll('.katex-error')].map(e => 'KaTeX: ' + (e.title || e.textContent)));
  return problems;
}

const disclosureState = () => ({
  details: [...document.querySelectorAll('details')].map(d => d.open),
  boxes: [...document.querySelectorAll('.collapsible')].map(d => d.classList.contains('open')),
  aria: [...document.querySelectorAll('.collapsible-header')].map(d => d.getAttribute('aria-expanded'))
});
const restoreDisclosureState = state => {
  document.querySelectorAll('details').forEach((d, i) => { d.open = state.details[i]; });
  document.querySelectorAll('.collapsible').forEach((d, i) => d.classList.toggle('open', state.boxes[i]));
  document.querySelectorAll('.collapsible-header').forEach((d, i) => {
    if (state.aria[i] === null) d.removeAttribute('aria-expanded');
    else d.setAttribute('aria-expanded', state.aria[i]);
  });
};
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const artifactInfo = filename => ({
  path: path.relative(process.cwd(), filename),
  bytes: fs.statSync(filename).size,
  sha256: crypto.createHash('sha256').update(fs.readFileSync(filename)).digest('hex')
});

export async function checkNativeBookExercises(page) {
  const result = {status:'passed', exercises:[], errors:[]};
  const exercises = page.locator('#book-lab details[id], main.book-content details[id^="book-project-"]');
  const candidates = await exercises.count();
  for (let i = 0; i < candidates; i++) {
    const exercise = exercises.nth(i);
    const title = (await exercise.locator(':scope > summary').textContent()).trim();
    if (!/^Exercise\b/.test(title)) continue;
    const record = {id:await exercise.getAttribute('id'), title, checks:[]};
    result.exercises.push(record);
    const saved = await exercise.evaluate(d => [d, ...d.querySelectorAll('details')].map(e => e.open));
    const check = (label, ok) => {
      record.checks.push({name:label, passed:ok});
      if (!ok) result.errors.push(record.id + ': ' + label);
    };
    try {
      const nestedTitles = await exercise.locator('details').evaluateAll(ds => ds.map(d => d.querySelector(':scope > summary')?.textContent.trim() || ''));
      const hintIndex = nestedTitles.findIndex(t => /^Show hint$/i.test(t));
      const solutionIndex = nestedTitles.findIndex(t => /^Show (?:worked )?solution$/i.test(t));
      if (hintIndex < 0 || solutionIndex < 0) throw new Error('Missing separate native hint/solution');
      const hint = exercise.locator('details').nth(hintIndex);
      const solution = exercise.locator('details').nth(solutionIndex);
      const hintBody = hint.locator(':scope > :not(summary)').first();
      const solutionBody = solution.locator(':scope > :not(summary)').first();
      const toggle = async (detail, key, expected) => {
        await detail.locator(':scope > summary').focus();
        await page.keyboard.press(key);
        await page.waitForFunction(({id, index, expected}) => {
          const outer = document.getElementById(id);
          return (index < 0 ? outer : outer.querySelectorAll('details')[index]).open === expected;
        }, {id:record.id, index:detail === exercise ? -1 : detail === hint ? hintIndex : solutionIndex, expected}, {timeout:2000});
        await settle(page, 20);
      };
      await exercise.evaluate(d => [d, ...d.querySelectorAll('details')].forEach(e => { e.open = false; }));
      await exercise.locator(':scope > summary').click();
      await settle(page, 20);
      check('Question opens on click', await exercise.evaluate(d => d.open));
      check('Question content is visible', await exercise.locator(':scope > :not(summary)').first().isVisible());
      check('Hint and solution start hidden', !await hintBody.isVisible() && !await solutionBody.isVisible());
      await toggle(hint, 'Enter', true);
      check('Enter opens hint content without solution', await hintBody.isVisible() && !await solutionBody.isVisible());
      await toggle(solution, 'Space', true);
      check('Space opens solution content independently', await hintBody.isVisible() && await solutionBody.isVisible());
      await toggle(hint, 'Space', false);
      check('Space closes hint while solution stays visible', !await hintBody.isVisible() && await solutionBody.isVisible());
      await toggle(solution, 'Enter', false);
      check('Enter closes solution content', !await solutionBody.isVisible());
      await toggle(exercise, 'Space', false);
      check('Space closes question content', !await exercise.locator(':scope > :not(summary)').first().isVisible());
      await toggle(exercise, 'Enter', true);
      check('Enter reopens question with answers still closed', await exercise.locator(':scope > :not(summary)').first().isVisible() && !await hintBody.isVisible() && !await solutionBody.isVisible());
    } catch (error) {
      result.errors.push(record.id + ': ' + error.message);
    } finally {
      await exercise.evaluate((d, states) => [d, ...d.querySelectorAll('details')].forEach((e, j) => { e.open = states[j]; }), saved);
    }
  }
  if (!result.exercises.length) Object.assign(result, {status:'skipped', reason:'No new book exercises on this page'});
  else if (result.errors.length) result.status = 'failed';
  return result;
}

async function checkAnchorInViewport(page, hash) {
  await page.evaluate(() => document.fonts.ready);
  await settle(page);
  await page.waitForFunction(hash => {
    if (decodeURIComponent(location.hash) !== hash) return false;
    const target = document.getElementById(hash.slice(1));
    if (!target) return false;
    const rect = target.getBoundingClientRect();
    return rect.top >= -2 && rect.top < innerHeight - 20;
  }, hash, {timeout:5000});
}

export async function checkBookNavigation(page) {
  const result = {status:'passed', applications:[], mobile:[], errors:[]};
  const startURL = page.url();
  const startViewport = page.viewportSize();
  const hrefs = await page.locator('.book-contents a[href$="#book-lab"]').evaluateAll(as => as.map(a => a.getAttribute('href')));
  if (hrefs.length !== 21) result.errors.push('Expected 21 contents-to-application links, found ' + hrefs.length);
  try {
    for (const href of hrefs) {
      const record = {href, contentsClick:false, localApplicationClick:false, returnClick:false};
      result.applications.push(record);
      try {
        await page.locator('.book-contents a[href=' + JSON.stringify(href) + ']').click();
        await checkAnchorInViewport(page, '#book-lab');
        if (new URL(page.url()).pathname !== new URL(href, startURL).pathname) throw new Error('Application click reached the wrong file');
        record.contentsClick = true;
        await page.locator('.book-entry a[href="#book-lab"]').click();
        await checkAnchorInViewport(page, '#book-lab');
        record.localApplicationClick = true;
        await page.locator('.book-entry a[href="book.html#book-contents"]').click();
        await checkAnchorInViewport(page, '#book-contents');
        if (new URL(page.url()).pathname !== new URL(startURL).pathname) throw new Error('Return click reached the wrong file');
        record.returnClick = true;
      } catch (error) {
        result.errors.push(href + ': ' + error.message);
        await page.goto(startURL, {waitUntil:'domcontentloaded'});
      }
    }
    await page.setViewportSize({width:390,height:900});
    for (const destination of ['case-studies.html', 'glossary.html', 'book.html']) {
      const record = {destination, menuClick:false, contentsReturn:false};
      result.mobile.push(record);
      try {
        await page.locator('.sidebar-open').click();
        await page.locator('#sidebar.open-mobile').waitFor({state:'visible'});
        await page.locator('#sidebar a.sidebar-link[href=' + JSON.stringify(destination) + ']').click();
        await page.waitForURL(url => url.pathname.endsWith('/' + destination));
        // A same-page sidebar link may leave the menu open. Dismiss before reading.
        if (await page.locator('#sidebar').evaluate(e => e.classList.contains('open-mobile')))
          await page.locator('.sidebar-toggle').click();
        await page.evaluate(() => document.fonts.ready);
        await settle(page);
        await page.locator('main h1').scrollIntoViewIfNeeded();
        const titleVisible = await page.locator('main h1').evaluate(e => { const r=e.getBoundingClientRect(); return r.top>=-2 && r.top<innerHeight; });
        if (!titleVisible) throw new Error('Destination title is outside the mobile viewport');
        record.menuClick = true;
        const returnLink = destination === 'book.html'
          ? page.locator('.page-toc a[href="#book-contents"]')
          : page.locator('main a[href="book.html#book-contents"]').last();
        await returnLink.click();
        await checkAnchorInViewport(page, '#book-contents');
        record.contentsReturn = true;
      } catch (error) {
        result.errors.push('Mobile ' + destination + ': ' + error.message);
        await page.goto(startURL, {waitUntil:'domcontentloaded'});
      }
    }
  } finally {
    await page.setViewportSize(startViewport);
    await page.goto(startURL, {waitUntil:'domcontentloaded'});
  }
  if (result.errors.length) result.status = 'failed';
  return result;
}

export const printRepresentatives = new Set(['book.html','primer-basics.html','toolkit-lmi.html','case-studies.html','glossary.html']);

export async function checkBookPrint(page, name, artifacts) {
  if (!printRepresentatives.has(name)) return {status:'skipped', reason:'Not one of the five representative print pages'};
  const result = {status:'passed', errors:[], pdf:null, syntheticGuard:null, lifecycle:null};
  const original = await page.evaluate(disclosureState);
  try {
    await page.evaluate(() => {
      document.querySelectorAll('details').forEach((d,i) => { d.open = i % 2 === 0; });
      document.querySelectorAll('.collapsible').forEach((d,i) => d.classList.toggle('open', i % 2 === 0));
      window.__bookQAPrintEvents = [];
      const snapshot = type => {
        const visible = e => { const s=getComputedStyle(e), r=e.getBoundingClientRect(); return s.display!=='none' && s.visibility!=='hidden' && r.width>0 && r.height>0; };
        const details = [...document.querySelectorAll('details')];
        const boxes = [...document.querySelectorAll('.collapsible')];
        const bodies = details.map(d => [...d.children].find(e => e.tagName!=='SUMMARY' && e.textContent.trim())).filter(Boolean);
        bodies.push(...document.querySelectorAll('.collapsible-body'));
        window.__bookQAPrintEvents.push({
          type, media:matchMedia('print').matches,
          state:{details:details.map(d=>d.open), boxes:boxes.map(d=>d.classList.contains('open')), aria:[...document.querySelectorAll('.collapsible-header')].map(d=>d.getAttribute('aria-expanded'))},
          hiddenNavigation:[...document.querySelectorAll('.sidebar,.sidebar-open,.skip-link,.page-nav,.book-entry,.page-toc')].map(e=>({selector:e.className, hidden:getComputedStyle(e).display==='none'})),
          reasoningBodies:bodies.length, hiddenReasoning:bodies.filter(e=>!visible(e)).map(e=>e.textContent.trim().slice(0,100))
        });
      };
      window.__bookQABeforePrint = () => snapshot('beforeprint');
      window.__bookQAAfterPrint = () => snapshot('afterprint');
      // Product listeners were registered during page load, so these run afterward.
      window.addEventListener('beforeprint', window.__bookQABeforePrint);
      window.addEventListener('afterprint', window.__bookQAAfterPrint);
    });
    const baseline = await page.evaluate(disclosureState);
    result.mixedState = {
      details:baseline.details.length, closedDetails:baseline.details.filter(v=>!v).length,
      boxes:baseline.boxes.length, closedBoxes:baseline.boxes.filter(v=>!v).length,
      openingApplicable:baseline.details.some(v=>!v) || baseline.boxes.some(v=>!v)
    };
    await page.evaluate(() => {
      window.dispatchEvent(new Event('beforeprint'));
      window.dispatchEvent(new Event('beforeprint'));
      window.dispatchEvent(new Event('afterprint'));
    });
    const guardEvents = await page.evaluate(() => window.__bookQAPrintEvents);
    const guardRestored = same(await page.evaluate(disclosureState), baseline);
    const guardOpened = guardEvents.filter(e=>e.type==='beforeprint').every(e=>e.state.details.every(Boolean) && e.state.boxes.every(Boolean));
    result.syntheticGuard = {status:guardEvents.length===3 && guardOpened && guardRestored ? 'passed':'failed', events:guardEvents.length, allOpened:guardOpened, exactRestoration:guardRestored};
    if (result.syntheticGuard.status==='failed') result.errors.push('Repeated beforeprint did not open and exactly restore the mixed disclosure state');
    await page.evaluate(restoreDisclosureState, baseline);
    await page.evaluate(() => { window.__bookQAPrintEvents = []; });
    await page.evaluate(() => document.fonts.ready);
    await page.emulateMedia({media:'print'});
    const filename = artifacts ? path.join(artifacts, name.replace(/\.html$/, '') + '-print.pdf') : undefined;
    const pdf = await page.pdf({...(filename ? {path:filename}:{}), format:'A4', printBackground:true});
    const validPDF = pdf.subarray(0,5).toString()==='%PDF-' && pdf.length>1000;
    result.pdf = {status:validPDF?'passed':'failed', ...(filename ? artifactInfo(filename) : {path:null,bytes:pdf.length,artifactStatus:'skipped',reason:'No artifact directory configured'}), visualInspection:'pending'};
    if (!validPDF) result.errors.push('PDF output is missing its header or unexpectedly small');
    await page.waitForFunction(() => window.__bookQAPrintEvents.some(e=>e.type==='afterprint'), null, {timeout:3000});
    const events = await page.evaluate(() => window.__bookQAPrintEvents);
    const before = events.filter(e=>e.type==='beforeprint');
    const after = events.filter(e=>e.type==='afterprint');
    const allOpened = before.length>0 && before.every(e=>e.state.details.every(Boolean) && e.state.boxes.every(Boolean));
    const exactRestoration = after.length>0 && after.every(e=>same(e.state,baseline)) && same(await page.evaluate(disclosureState),baseline);
    const printCSS = before.length>0 && before.every(e=>e.media && e.hiddenNavigation.every(n=>n.hidden) && !e.hiddenReasoning.length);
    result.lifecycle = {status:allOpened && exactRestoration && printCSS ? 'passed':'failed', beforeEvents:before.length, afterEvents:after.length, allOpened, exactRestoration, printCSS, events};
    if (!allOpened) result.errors.push('Actual PDF beforeprint did not open every disclosure');
    if (!exactRestoration) result.errors.push('Actual PDF afterprint did not exactly restore the mixed disclosure state');
    if (!printCSS) result.errors.push('Print media did not hide navigation and reveal reasoning bodies');
  } catch (error) {
    result.errors.push(error.message);
  } finally {
    await page.emulateMedia({media:null});
    // Clear a pending product print snapshot even when PDF generation failed.
    await page.evaluate(() => window.dispatchEvent(new Event('afterprint')));
    await page.evaluate(restoreDisclosureState, original);
    await page.evaluate(() => {
      window.removeEventListener('beforeprint', window.__bookQABeforePrint);
      window.removeEventListener('afterprint', window.__bookQAAfterPrint);
      delete window.__bookQABeforePrint; delete window.__bookQAAfterPrint; delete window.__bookQAPrintEvents;
    });
  }
  if (result.errors.length) result.status = 'failed';
  return result;
}

export async function captureBookScreenshot(page, name, width, artifacts) {
  if (!artifacts) return {status:'skipped', reason:'No artifact directory configured'};
  const target = page.locator('#book-lab, main.book-content').first();
  if (!await target.count()) return {status:'skipped', reason:'No application lab or book reference content'};
  await page.evaluate(() => document.fonts.ready);
  await settle(page);
  const filename = path.join(artifacts, name.replace(/\.html$/, '') + '-' + width + '.png');
  const box = await target.boundingBox();
  await target.screenshot({path:filename, animations:'disabled'});
  return {status:'passed', viewportWidth:width, target:await target.getAttribute('id') || 'main.book-content', dimensions:{width:box.width,height:box.height}, ...artifactInfo(filename), visualInspection:'pending'};
}
