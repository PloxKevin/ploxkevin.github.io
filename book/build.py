#!/usr/bin/env python3
"""Integrate authored book material without rewriting the audited chapter bodies."""
from pathlib import Path
import html
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'SafeLearning'
primers = json.loads((ROOT/'primers_plan.json').read_text())
modules = json.loads((ROOT/'modules_min.json').read_text())['modules']
chapters = primers['primers'] + modules
references = [
    dict(id='book',num='↗',title='The Book & Reading Path',file='book.html',sections=[
        ['book-purpose','What This Book Teaches'],['book-method','How to Study'],
        ['book-contents','Complete Reading Path'],['book-cases','Connected Projects'],
        ['book-progress','Judge Your Progress'],['book-conventions','Conventions and Evidence']]),
    dict(id='case-studies',num='↗',title='Projects & Connected Cases',file='case-studies.html',sections=[
        ['case-tank','Measured Tank'],['case-tuning','Safe Controller Tuning'],
        ['case-score','Learned Decisions'],['case-report','Write an Engineering Argument']]),
    dict(id='glossary',num='↗',title='Glossary & Notation',file='glossary.html',sections=[
        ['glossary-language','Mathematical Language'],['glossary-linear','Linear Algebra'],
        ['glossary-optimization','Optimization'],['glossary-probability','Probability'],
        ['glossary-control','Systems and Control'],['glossary-learning','Learning and Certificates'],
        ['glossary-symbols','Symbols in Context']]),
]

def marked(source, key, body, before):
    start=f'<!-- BOOK {key} START -->';end=f'<!-- BOOK {key} END -->'
    block=start+'\n'+body.strip()+'\n'+end+'\n'
    if start in source:
        return re.sub(re.escape(start)+r'.*?'+re.escape(end)+r'\n?',lambda _:block,source,flags=re.S)
    assert source.count(before)==1,(key,before,source.count(before))
    return source.replace(before,block+before,1)

for chapter in chapters:
    path=SITE/chapter['file'];source=path.read_text()
    fragment=(ROOT/'book/chapters'/chapter['file']).read_text()
    assert fragment.count('id="book-lab"')==1,path
    source=marked(source,'APPLICATION',fragment,'<h2 class="section-heading" id="exercises">')
    if 'href="#book-lab"' not in source:
        pattern=r'(?m)^([ \t]*)(<a href="#exercises">[^<]*</a>)'
        assert len(re.findall(pattern,source))==1,path
        source=re.sub(pattern,lambda m:m[1]+'<a href="#book-lab">Application lab &amp; chapter review</a>\n'+m[1]+m[2],source,count=1)
    # Preserve the original indentation of the adjacent exercise TOC entry.
    source=re.sub(r'(?m)^([ \t]*)(<a href="#book-lab">Application lab &amp; chapter review</a>)\n[ \t]*(<a href="#exercises">[^<]*</a>)',
                  lambda m:m[1]+m[2]+'\n'+m[1]+m[3],source)
    entry='<p class="book-entry"><a href="book.html#book-contents">Book contents</a> &middot; <a href="#book-lab">Apply this chapter to a real decision</a> &middot; <a href="glossary.html">Glossary</a></p>'
    source=marked(source,'ENTRY',entry,'<div class="page-toc">')
    path.write_text(source)

catalog=[]
for heading,group in [('Part I — Mathematical foundations',chapters[:6]),
                      ('Part II — Safety and the mathematical toolkit',chapters[6:9]),
                      ('Part III — Safe exploration',chapters[9:13]),
                      ('Part IV — Constrained learning and control',chapters[13:17]),
                      ('Part V — Certified neural networks and verification',chapters[17:])]:
    catalog.append('<h3 class="subsection-heading">'+html.escape(heading)+'</h3><ol class="book-contents">')
    for c in group:
        catalog.append(f'<li><a href="{c["file"]}">{html.escape(c["num"]+". "+c["title"])}</a> — <a href="{c["file"]}#book-lab">application and review</a></li>')
    catalog.append('</ol>')

def page(title, content, active):
    return '''<!DOCTYPE html>
<html lang="en"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>'''+html.escape(title)+''' — Safe Learning</title>
<link rel="stylesheet" href="style.css">
<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.css">
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/katex.min.js"></script>
<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.9/dist/contrib/auto-render.min.js" onload="renderMathInElement(document.body,{delimiters:[{left:'$$',right:'$$',display:true},{left:'$',right:'$',display:false}]});"></script>
</head><body><nav id="sidebar" class="sidebar"></nav><button class="sidebar-open" onclick="toggleSidebar()">&#9776;</button>
<main class="main-content book-content">'''+content+'''
<div class="page-nav"><a href="book.html">Book contents</a><a href="primer-basics.html">Begin at Chapter0 &rarr;</a></div>
</main><script src="components.js"></script><script>renderSidebar('''+json.dumps(active)+''');initCollapsibles();</script></body></html>
'''

for ref,fragment in zip(references,['frontmatter.html','case-studies.html','glossary.html']):
    content=(ROOT/'book'/fragment).read_text().replace('<!-- BOOK CHAPTER CATALOG -->','\n'.join(catalog))
    (SITE/ref['file']).write_text(page(ref['title'],content,ref['id']))

# Preserve the hand-maintained engine; update only the declarative sidebar data.
js_path=SITE/'components.js';js_source=js_path.read_text();split=js_source.index('// === SIDEBAR ===')
data=json.loads(subprocess.check_output(['node','-e',
    'const fs=require("fs"),vm=require("vm");let s=fs.readFileSync(process.argv[1],"utf8");'
    'console.log(JSON.stringify(vm.runInNewContext(s.slice(0,s.indexOf("// === SIDEBAR ==="))+";MODULES;",{})))',
    str(js_path)],text=True))
owned={c['file'] for c in chapters}
for cluster in data:
    for module in cluster['modules']:
        if module['file'] in owned and not any(s['id']=='book-lab' for s in module['sections']):
            index=next(i for i,s in enumerate(module['sections']) if s['id']=='exercises')
            module['sections'].insert(index,dict(name='Application Lab & Chapter Review',id='book-lab'))
    if cluster['cluster']=='Reference':
        cluster['modules']=[m for m in cluster['modules'] if m['id'] not in {r['id'] for r in references}]
        cluster['modules'][:0]=[{**r,'sections':[dict(id=i,name=n) for i,n in r['sections']]} for r in references]
js_path.write_text('// === MODULE DATA ===\nconst MODULES = '+json.dumps(data,ensure_ascii=False,indent=2)+';\n\n'+js_source[split:])

# Keep source metadata compatible with a later gen.mjs regeneration.
for p in primers['primers']:
    if not any(s[0]=='book-lab' for s in p['sections']):p['sections'].append(['book-lab','Application Lab & Chapter Review'])
(ROOT/'primers_plan.json').write_text(json.dumps(primers,ensure_ascii=False,indent=2)+'\n')
curr_path=ROOT/'curriculum.mjs';curr=curr_path.read_text()
if '// === BOOK APPLICATION SECTIONS ===' not in curr:
    hook='''// === BOOK APPLICATION SECTIONS ===
for (const module of MODULES) {
  if (!module.sections.some(([id]) => id === 'book-lab')) {
    const i = module.sections.findIndex(([id]) => id === 'exercises');
    module.sections.splice(i, 0, ['book-lab', 'Application Lab & Chapter Review']);
  }
}

'''
    curr=curr.replace('export const REFERENCE = [',hook+'export const REFERENCE = [',1)
if '// Book front matter and projects' not in curr:
    entries=[{**r,'cluster':'reference'} for r in references]
    curr=curr.replace('export const REFERENCE = [','export const REFERENCE = [\n  // Book front matter and projects\n  '+',\n  '.join(json.dumps(r,ensure_ascii=False) for r in entries)+',',1)
curr_path.write_text(curr)

landing=SITE/'index.html';text=landing.read_text()
text=marked(text,'WELCOME','''<div class="insight-box"><div class="box-label">Read this as a book</div><p>Follow the <a href="book.html">complete reading path</a> through six foundation chapters and fifteen learning/control chapters. Each now includes a practical application lab, chapter review and new transfer exercises. Finish with <a href="case-studies.html">three connected projects</a>; use the <a href="glossary.html">glossary</a> when a term needs rebuilding.</p></div>''','    <!-- Concept Map -->')
text=text.replace('Interactive research notes &mdash; safe RL, safe learning-based control &amp; certified neural networks','An educational book with interactive chapters, worked examples and graded practice')
landing.write_text(text)
guide=SITE/'study-guide.html';text=guide.read_text()
text=marked(text,'GUIDE','''<div class="insight-box"><div class="box-label">A book route with connected decisions</div><p>The <a href="book.html">book front matter</a> explains the learning path and how to judge progress. Read a chapter’s theory, attempt its application lab, then reconstruct the decision with changed assumptions. The <a href="case-studies.html">projects</a> connect several chapters; the <a href="glossary.html">glossary</a> links terminology to small examples.</p></div>''','    <div class="page-toc">')
guide.write_text(text)
(ROOT/'reports/book/catalog.json').write_text(json.dumps(dict(chapters=[{k:c[k] for k in ['id','num','file','title']} for c in chapters],references=references),ensure_ascii=False,indent=2)+'\n')
print('Integrated21chapter labs, book front matter, projects, glossary and navigation.')
