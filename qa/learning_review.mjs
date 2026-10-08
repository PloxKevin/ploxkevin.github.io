// Whole-site reader QA. Run from repository root; default: every SafeLearning HTML page.
import { chromium } from 'playwright-core';
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import { pathToFileURL } from 'node:url';
import { settle, renderedMathProblems, checkNativeBookExercises, checkBookNavigation,
  checkBookPrint, captureBookScreenshot } from './book_browser_checks.mjs';

const args = process.argv.slice(2);
function option(flag, fallback) {
  const index = args.indexOf(flag);
  if (index < 0) return fallback;
  if (!args[index+1] || args[index+1].startsWith('--')) throw new Error(flag + ' requires a path');
  return args.splice(index, 2)[1];
}
const reportPath = path.resolve(option('--report', 'reports/learning-review/browser-final.json'));
const bookReportRoot = path.resolve('reports/book');
const underBookReports = reportPath.startsWith(bookReportRoot + path.sep);
const artifactOption = option('--artifacts', underBookReports ? 'reports/book/browser-artifacts' : null);
const artifacts = artifactOption ? path.resolve(artifactOption) : null;
if (args.some(arg=>arg.startsWith('--'))) throw new Error('Unknown option: ' + args.find(arg=>arg.startsWith('--')));
const site = path.resolve(process.env.SAFELEARNING_QA_SITE || 'SafeLearning');
const files = args.length ? args : fs.readdirSync(site).filter(f => f.endsWith('.html')).sort();
const qaSources = Object.fromEntries(['learning_review.mjs','book_browser_checks.mjs'].map(name=>[name,crypto.createHash('sha256').update(fs.readFileSync(new URL(name,import.meta.url))).digest('hex')]));
const report = files.map(name=>({file:name,qa_source_sha256:qaSources,status:'pending',errors:[],exerciseCounts:{},viewports:[],screenshots:[],checks:Object.fromEntries(['browser','nativeBookExercises','bookNavigation','print','dynamicMath','sliderLimits','screenshots'].map(check=>[check,{status:'pending'}]))}));
const writeReport = () => {
  fs.mkdirSync(path.dirname(reportPath),{recursive:true});
  const temporary = reportPath + '.tmp-' + process.pid;
  fs.writeFileSync(temporary,JSON.stringify(report,null,2));
  fs.renameSync(temporary,reportPath);
};
// Persist the full requested inventory before launching or visiting any page.
// Atomic replacement retains the last complete JSON snapshot if interrupted.
writeReport();
let browser;
try {
  browser = await chromium.launch({
    executablePath: process.env.SAFELEARNING_CHROMIUM || process.env.HOME + '/.cache/ms-playwright/chromium_headless_shell-1208/chrome-headless-shell-linux64/chrome-headless-shell'
  });
} catch (error) {
  // A launch failure is evidence of a blocked run, never a passing empty report.
  report.splice(0,report.length,{file:null,status:'blocked',requestedFiles:files,site,artifactDirectory:artifacts,qa_source_sha256:qaSources,errors:['Browser launch: ' + error.message],checks:{browser:{status:'blocked'},nativeBookExercises:{status:'skipped',reason:'Browser did not launch'},bookNavigation:{status:'skipped',reason:'Browser did not launch'},print:{status:'skipped',reason:'Browser did not launch'},screenshots:{status:'skipped',reason:'Browser did not launch'}}});
  writeReport();
  throw error;
}
if (artifacts) fs.mkdirSync(artifacts,{recursive:true});

for (const [index,name] of files.entries()) {
  const file = path.join(site, name);
  const fingerprint = () => crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex');
  const r = report[index];
  r.status = 'running';
  writeReport();
  let page;
  try {
    r.source_sha256 = fingerprint();
    page = await browser.newPage({viewport:{width:1280,height:900}});
    r.checks.browser = {status:'passed'};
    page.on('pageerror', e => r.errors.push('Runtime: ' + e.message));
    page.on('console', m => { if (m.type() === 'error') r.errors.push('Console: ' + m.text()); });
    await page.goto(pathToFileURL(file).href, {waitUntil:'networkidle'});
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
    const teachingPage = !['index.html','study-guide.html','formulas.html','papers.html','open-problems.html','book.html','case-studies.html','glossary.html'].includes(name);
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
    r.checks.nativeBookExercises = await checkNativeBookExercises(page);
    const expectedBookExercises = name==='case-studies.html' ? 9 : name.startsWith('primer-') ? 4 : teachingPage ? ['cmdp.html','policy-optimization.html','barriers.html','lyapunov-mpc.html'].includes(name) ? 3 : 2 : 0;
    r.checks.nativeBookExercises.expectedExercises = expectedBookExercises;
    if (r.checks.nativeBookExercises.exercises.length!==expectedBookExercises) {
      r.checks.nativeBookExercises.status='failed';
      r.checks.nativeBookExercises.errors.push('Expected ' + expectedBookExercises + ' new book exercises, checked ' + r.checks.nativeBookExercises.exercises.length);
    }
    r.errors.push(...r.checks.nativeBookExercises.errors);
    r.checks.bookNavigation = name === 'book.html'
      ? await checkBookNavigation(page)
      : {status:'skipped',reason:'The complete contents/application/return route is checked from book.html'};
    r.errors.push(...(r.checks.bookNavigation.errors || []));
    r.checks.print = await checkBookPrint(page, name, artifacts);
    r.errors.push(...(r.checks.print.errors || []));
    const dynamicMath = await page.evaluate(source => {
      const mathProblems = eval('(' + source + ')');
      const found = [];
      let walkthroughs=0, walkthroughSteps=0, flashcards=0, flashcardFaces=0;
      document.querySelectorAll('*').forEach(el => {
        if (el._walkthrough) {
          walkthroughs++;
          const n = el.querySelectorAll('.walkthrough-step-tab').length;
          for (let i=0;i<n;i++) {
            walkthroughSteps++;
            el._walkthrough.goTo(i);
            found.push(...mathProblems(el).map(problem=>'Walkthrough step ' + i + ': ' + problem));
            if ([...el.querySelectorAll('.walkthrough-step-tab')].some(tab => tab.tagName !== 'BUTTON'))
              found.push('Walkthrough steps must be buttons');
          }
          el._walkthrough.goTo(0);
        }
        if (el._state?.cards) {
          flashcards++;
          for (let i=0;i<el._state.cards.length;i++) {
            flashcardFaces++;
            el._state.setIndex(i); el._state.reveal(); el._state.render();
            found.push(...mathProblems(el).map(problem=>'Flashcard ' + i + ': ' + problem));
          }
          el._state.setIndex(0); el._state.render();
        }
      });
      return {errors:found,walkthroughs,walkthroughSteps,flashcards,flashcardFaces};
    }, renderedMathProblems.toString());
    r.errors.push(...dynamicMath.errors.map(s => 'Dynamic math: ' + s));
    r.checks.dynamicMath = {status:dynamicMath.walkthroughs+dynamicMath.flashcards ? dynamicMath.errors.length?'failed':'passed' : 'skipped',...dynamicMath};
    if (r.checks.dynamicMath.status==='skipped') r.checks.dynamicMath.reason='No walkthroughs or flashcards on this page';
    const sliders = await page.locator('input[type=range]').count();
    r.sliderCount = sliders;
    r.sliderSamples = [];
    for (let i=0;i<sliders;i++) {
      const slider = page.locator('input[type=range]').nth(i);
      const state = await slider.evaluate(el=>({initial:el.value,min:el.min||'0',max:el.max||'100',id:el.id}));
      for (const [label,value] of [['minimum',state.min],['maximum',state.max],['initial',state.initial]]) {
        const errorStart = r.errors.length;
        await slider.evaluate((el,value) => {
          el.value=value;
          el.dispatchEvent(new Event('input',{bubbles:true}));
          el.dispatchEvent(new Event('change',{bubbles:true}));
        }, value);
        // Let RAF/debounced explorers render each limit before restoring the slider.
        await settle(page, 250);
        const problems = await page.locator('body').evaluate(renderedMathProblems);
        const actual = await slider.inputValue();
        const readouts = await slider.evaluate(el => {
          const container = el.closest('.interactive-container,.interactive-box,.explorer') || el.parentElement;
          const associated = el.id ? [document.getElementById(el.id+'-val'),document.getElementById(el.id+'-v')].filter(Boolean) : [];
          const nodes = [...new Set([...associated,...container.querySelectorAll('output,[aria-live],.slider-value,.value-display,span[id$="-val"],span[id$="-v"]')])].slice(0,20);
          return nodes.map(e=>({id:e.id||null,text:e.textContent.trim(),associated:associated.includes(e)}));
        });
        r.sliderSamples.push({index:i,id:state.id,label,requested:value,actual,readouts,mathErrors:problems,runtimeErrors:r.errors.slice(errorStart)});
        if (Number(actual)!==Number(value)) r.errors.push('Slider ' + i + ' did not retain ' + label + ' value');
        r.errors.push(...problems.map(s=>'Slider ' + i + ' ' + label + ': ' + s));
      }
    }
    r.checks.sliderLimits = sliders
      ? {status:r.sliderSamples.some(s=>s.mathErrors.length || s.runtimeErrors.length || Number(s.actual)!==Number(s.requested))?'failed':'passed',kind:'Input/error smoke',samples:r.sliderSamples.length,settle:'Two animation frames plus 250 ms per value',scope:'Checks retained input values and rendered math/runtime errors after settling; captures associated value labels for review',explorerNumericalCorrectness:'not_checked'}
      : {status:'skipped',reason:'No range inputs on this page'};
    r.errors.push(...await page.locator('body').evaluate(renderedMathProblems));
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
      if (width===390 || width===1280) {
        try {
          r.screenshots.push(await captureBookScreenshot(page,name,width,artifacts));
        } catch (error) {
          r.screenshots.push({status:'failed',viewportWidth:width,error:error.message});
          r.errors.push('Screenshot at ' + width + ': ' + error.message);
        }
      }
    }
    r.checks.screenshots = {status:r.screenshots.some(s=>s.status==='failed')?'failed':r.screenshots.some(s=>s.status==='passed')?'passed':'skipped', artifacts:r.screenshots.filter(s=>s.status==='passed').length, visualInspection:'pending'};
    for (const screenshot of r.screenshots) screenshot.source_sha256 = r.source_sha256;
    if (r.checks.print.pdf) r.checks.print.pdf.source_sha256 = r.source_sha256;
  } catch (error) {
    r.errors.push('Unexpected page failure: ' + (error.message || String(error)));
  } finally {
    if (page) {
      try { await page.close(); }
      catch (error) { r.errors.push('Page cleanup: ' + (error.message || String(error))); }
    }
    if (r.source_sha256) {
      try {
        if (fingerprint()!==r.source_sha256) r.errors.push('Source changed during browser verification');
      } catch (error) { r.errors.push('Source fingerprint: ' + (error.message || String(error))); }
    }
    for (const check of Object.values(r.checks))
      if (check.status==='pending') Object.assign(check,{status:'skipped',reason:'Page processing stopped before this check'});
    r.errors = [...new Set(r.errors)];
    r.status = r.errors.length ? 'failed':'passed';
    writeReport();
    console.log(name + ': ' + (r.exerciseCounts.total ?? '?') + ' exercises; ' + r.errors.length + ' issues');
    if (r.errors.length) console.log(JSON.stringify(r.errors));
  }
}
try { await browser.close(); }
catch (error) {
  if (report.length) {
    const r = report.at(-1);
    r.errors.push('Browser cleanup: ' + (error.message || String(error)));
    r.status = 'failed';
    writeReport();
  }
  process.exitCode=1;
}
if (!report.length || report.some(r => r.status!=='passed')) process.exitCode=1;
