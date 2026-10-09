#!/usr/bin/env python3
"""Independently validate static book integration without modifying site sources.

Checks 29 HTML pages, local HTML/asset references, fragment anchors, unique IDs,
all 21 application labs, native exercise structure, sidebar/catalog consistency,
and byte-for-byte preservation of the original 21 teaching pages after removing
only the documented book insertions. No browser or JavaScript UI is executed.
Writes only book/review/integration.json; historic reports/baselines are inputs.
"""
from collections import Counter
from dataclasses import dataclass, field
from datetime import datetime, timezone
from html.parser import HTMLParser
from pathlib import Path
from typing import Iterator
from urllib.parse import unquote, urlsplit
import argparse
import difflib
import hashlib
import json
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SITE = ROOT / 'SafeLearning'
BASELINE = ROOT / 'reports/book/baseline'
REPORT = ROOT / 'book/review/integration.json'
VOID = {'area','base','br','col','embed','hr','img','input','link','meta','param','source','track','wbr'}


@dataclass
class Node:
    tag: str
    attrs: dict
    line: int
    children: list = field(default_factory=list)

    def text(self) -> str:
        return ''.join(c.text() if isinstance(c, Node) else c for c in self.children)

    def descendants(self, tag=None) -> Iterator['Node']:
        for c in self.children:
            if isinstance(c, Node):
                if tag is None or c.tag == tag:
                    yield c
                yield from c.descendants(tag)

    def child(self, tag):
        return next((c for c in self.children if isinstance(c, Node) and c.tag == tag), None)


class Document(HTMLParser):
    def __init__(self, source):
        super().__init__(convert_charrefs=True)
        self.source = source
        self.root = Node('document', {}, 1)
        self.stack = [self.root]
        self.nodes = []
        self.feed(source)
        self.ids = [n.attrs['id'] for n in self.nodes if 'id' in n.attrs]
        self.by_id = {n.attrs['id']: n for n in self.nodes if 'id' in n.attrs}

    def handle_starttag(self, tag, attrs):
        n = Node(tag, dict(attrs), self.getpos()[0])
        self.stack[-1].children.append(n)
        self.nodes.append(n)
        if tag not in VOID:
            self.stack.append(n)

    def handle_startendtag(self, tag, attrs):
        self.handle_starttag(tag, attrs)
        if tag not in VOID:
            self.handle_endtag(tag)

    def handle_endtag(self, tag):
        for i in range(len(self.stack)-1, 0, -1):
            if self.stack[i].tag == tag:
                self.stack = self.stack[:i]
                return

    def handle_data(self, data):
        self.stack[-1].children.append(data)


def digest(source):
    return hashlib.sha256(source.encode()).hexdigest()


def clean_text(text):
    return re.sub(r'\s+', ' ', text).strip()


def level_of(summary):
    m = re.search(r'^[ \t]*(Easy|Medium|Hard)\s+\d+\b|[—–-]\s*(Easy|Medium|Hard)\s*:', summary, re.I)
    return (m.group(1) or m.group(2)).capitalize() if m else None


def exercises(root):
    out = []
    for n in root.descendants('details'):
        summary = n.child('summary')
        label = clean_text(summary.text()) if summary else ''
        if not re.match(r'^(Exercise\b|(Easy|Medium|Hard)\s+\d+\b)', label, re.I):
            continue
        nested = [clean_text(s.text()) for s in n.descendants('summary') if s is not summary]
        out.append(dict(id=n.attrs.get('id'), line=n.line, summary=label,
                        level=level_of(label),
                        has_hint=any(re.search(r'\bhint\b', s, re.I) for s in nested),
                        has_solution=any(re.search(r'\b(answer|solution)\b', s, re.I) for s in nested)))
    return out


def counts(items):
    c = Counter(x['level'] or 'ungraded' for x in items)
    return dict(total=len(items), Easy=c['Easy'], Medium=c['Medium'], Hard=c['Hard'], ungraded=c['ungraded'])


def remove_insertions(source):
    """Remove only insertion spans and the single added book TOC item.

    Whitespace outside those exact spans is retained, permitting a byte-equality
    check against the historical baseline rather than a weaker text-only check.
    """
    for key in ('APPLICATION', 'ENTRY'):
        pattern = rf'<!-- BOOK {key} START -->.*?<!-- BOOK {key} END -->\n?'
        source = re.sub(pattern, '', source, flags=re.S)
    source = re.sub(r'[ \t]*<a href="#book-lab">Application lab &amp; chapter review</a>\n', '', source)
    return source


def sidebar_data(js):
    prefix = js.split('// === SIDEBAR ===', 1)[0]
    m = re.search(r'\bconst\s+MODULES\s*=\s*(\[.*\])\s*;', prefix, re.S)
    if m:
        try:
            return json.loads(m.group(1))
        except json.JSONDecodeError:
            pass
    # The historical declaration can use JS object syntax. Evaluate only the
    # declarative prefix in an empty VM context; never execute the DOM engine.
    result = subprocess.run(['node', '-e',
        'const fs=require("fs"),vm=require("vm");'
        'const s=fs.readFileSync(process.argv[1],"utf8");'
        'process.stdout.write(JSON.stringify(vm.runInNewContext(s+";MODULES;",{})));',
        '/dev/stdin'], input=prefix, text=True, capture_output=True, check=True)
    return json.loads(result.stdout)


def build_idempotence():
    """Exercise the real build twice in a disposable copy, never in the site.

    The build chooses its root relative to its own path, so copying its inputs
    preserves its behavior while confining all mutations to a temporary tree.
    """
    with tempfile.TemporaryDirectory(prefix='safelearning-book-build-') as directory:
        trial=Path(directory)
        (trial/'book').mkdir()
        (trial/'reports/book').mkdir(parents=True)
        shutil.copytree(SITE,trial/'SafeLearning')
        shutil.copytree(ROOT/'book/chapters',trial/'book/chapters')
        for name in ('build.py','frontmatter.html','case-studies.html','glossary.html'):
            shutil.copyfile(ROOT/'book'/name,trial/'book'/name)
        for name in ('primers_plan.json','modules_min.json','curriculum.mjs'):
            shutil.copyfile(ROOT/name,trial/name)
        shutil.copyfile(ROOT/'reports/book/catalog.json',trial/'reports/book/catalog.json')

        def hashes():
            return {str(p.relative_to(trial)):hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in sorted(trial.rglob('*')) if p.is_file()}

        before=hashes()
        first=subprocess.run([sys.executable,str(trial/'book/build.py')],cwd=trial,
                             capture_output=True,text=True,check=True)
        after_first=hashes()
        second=subprocess.run([sys.executable,str(trial/'book/build.py')],cwd=trial,
                              capture_output=True,text=True,check=True)
        after_second=hashes()
        delta=lambda a,b:sorted(k for k in a.keys()|b.keys() if a.get(k)!=b.get(k))
        return dict(execution_scope='Disposable temporary copy; no site or historical report files mutated.',
                    initial_rebuild_changed_files=delta(before,after_first),
                    second_rebuild_changed_files=delta(after_first,after_second),
                    current_root_already_matches_build=before==after_first,
                    repeated_build_is_byte_idempotent=after_first==after_second,
                    first_stdout=first.stdout.strip(),second_stdout=second.stdout.strip(),
                    files_compared=len(after_second))


def validate(allow_reviewed_corrections=False):
    errors = []
    warnings = []
    checks = []
    pages = {}
    source_reports = []
    corrections_path=ROOT/'book/coverage/material-corrections.json'
    corrections=(json.loads(corrections_path.read_text())['corrections']
                 if allow_reviewed_corrections else [])

    def error(category, file, message, **extra):
        errors.append(dict(category=category, file=file, message=message, **extra))

    def passed(name, **detail):
        checks.append(dict(check=name, **detail))

    html_files = sorted(SITE.glob('*.html'))
    for path in html_files:
        source = path.read_text()
        doc = Document(source)
        pages[path.name] = doc
        dup = [i for i, n in Counter(doc.ids).items() if n > 1]
        for ident in dup:
            error('duplicate_id', path.name, 'ID appears more than once', anchor=ident)
    if len(pages) != 29:
        error('page_count', 'SafeLearning/', 'Expected exactly 29 HTML pages', actual=len(pages), expected=29)
    passed('Parsed all static HTML pages', count=len(pages))

    local_reference_count = 0
    external_reference_count = 0
    # Validate static attributes as paths, not merely anchor hrefs. Dynamic JS
    # sidebar paths are validated independently from their metadata below.
    for name, doc in pages.items():
        for n in doc.nodes:
            attrs = [k for k in ('href', 'src', 'poster') if k in n.attrs]
            if n.tag == 'object' and 'data' in n.attrs:
                attrs.append('data')
            for attr in attrs:
                value = n.attrs[attr] or ''
                split = urlsplit(value)
                if split.scheme or split.netloc:
                    external_reference_count += 1
                    continue
                local_reference_count += 1
                target = ((SITE / unquote(split.path)) if split.path else SITE/name).resolve()
                if not target.exists():
                    error('missing_local_path', name, 'Local target does not exist', line=n.line, attribute=attr, target=value)
                    continue
                if split.fragment and target.suffix.lower() in ('.html', '.htm'):
                    anchor = unquote(split.fragment)
                    if target.parent == SITE.resolve() and target.name in pages:
                        target_doc = pages[target.name]
                    else:
                        target_doc = Document(target.read_text())
                    if anchor not in target_doc.by_id:
                        error('missing_anchor', name, 'Static local anchor does not exist', line=n.line, target=value, anchor=anchor)
    passed('Static HTML references checked', local=local_reference_count, external_not_fetched=external_reference_count)

    catalog_path = ROOT/'reports/book/catalog.json'
    catalog = json.loads(catalog_path.read_text())
    primers = json.loads((ROOT/'primers_plan.json').read_text())['primers']
    modules = json.loads((ROOT/'modules_min.json').read_text())['modules']
    expected_chapters = primers + modules
    expected_files = [c['file'] for c in expected_chapters]
    catalog_files = [c['file'] for c in catalog['chapters']]
    if len(expected_files) != 21 or catalog_files != expected_files:
        error('catalog_chapters', 'reports/book/catalog.json', 'Catalog does not match the 21 primer/module files in order',
              expected=expected_files, actual=catalog_files)
    for expected, recorded in zip(expected_chapters, catalog['chapters']):
        for key in ('id', 'num', 'file', 'title'):
            if expected[key] != recorded[key]:
                error('catalog_field', 'reports/book/catalog.json', 'Chapter catalog field differs from source metadata', chapter=expected['id'], field=key)

    preservation = []
    lab_reports = []
    total_new_exercises = 0
    total_baseline_exercises = 0
    all_exercises = []
    new_exercise_labels = []
    for name, doc in pages.items():
        items = exercises(doc.root)
        all_exercises.extend((name, x) for x in items)
        for x in items:
            if not x['has_solution']:
                error('exercise_solution', name, 'Exercise lacks a native answer/solution disclosure', exercise=x['summary'], line=x['line'])
            if x['level'] and not x['has_hint']:
                error('exercise_hint', name, 'Graded exercise lacks a separate native hint disclosure', exercise=x['summary'], line=x['line'])

    for name in expected_files:
        if name not in pages:
            error('missing_chapter', name, 'Catalog chapter file is missing')
            continue
        doc = pages[name]
        source_path = ROOT/'book/chapters'/name
        if not source_path.exists():
            error('missing_fragment', str(source_path.relative_to(ROOT)), 'Authoritative chapter fragment is missing')
            continue
        source = source_path.read_text()
        fragment = Document(source)
        source_lab = fragment.by_id.get('book-lab')
        lab = doc.by_id.get('book-lab')
        if lab is None:
            error('missing_lab', name, 'Chapter has no book-lab section')
            continue
        if source_lab is None:
            error('missing_source_lab', str(source_path.relative_to(ROOT)), 'Authoritative fragment has no book-lab section')
            continue
        if lab.tag != 'section' or 'book-chapter' not in (lab.attrs.get('class') or '').split():
            error('lab_structure', name, 'book-lab must be a section with class book-chapter')
        h2 = lab.child('h2')
        if not h2 or clean_text(h2.text()) != 'From the mathematics to a real decision':
            error('lab_heading', name, 'Lab has a missing or changed top heading')
        # The integration marker encloses exactly the authoritative fragment.
        blocks = re.findall(r'<!-- BOOK APPLICATION START -->\n?(.*?)\n?<!-- BOOK APPLICATION END -->', doc.source, re.S)
        if len(blocks) != 1 or blocks[0].strip() != source.strip():
            error('stale_integrated_fragment', name, 'Integrated application differs from its current authoritative fragment',
                  fragment=str(source_path.relative_to(ROOT)))
        if doc.source.count('<!-- BOOK ENTRY START -->') != 1:
            error('entry_marker', name, 'Expected exactly one book entry insertion')
        if doc.source.count('<a href="#book-lab">Application lab &amp; chapter review</a>') != 1:
            error('lab_toc', name, 'Expected exactly one application TOC link')
        if 'exercises' not in doc.by_id or doc.ids.index('book-lab') >= doc.ids.index('exercises'):
            error('lab_order', name, 'Application must precede the original exercise section')
        new_items = exercises(lab)
        source_items = exercises(source_lab)
        if [(x['id'],x['summary']) for x in new_items] != [(x['id'],x['summary']) for x in source_items]:
            error('exercise_integration', name, 'Integrated lab exercises differ from authoritative fragment')
        minimum = 4 if name.startswith('primer-') else 2
        if len(new_items) < minimum:
            error('new_exercise_count', name, 'Application has too few exercises', actual=len(new_items), minimum=minimum)
        for x in new_items:
            if not x['level']:
                error('new_exercise_level', name, 'New exercise lacks Easy/Medium/Hard label', exercise=x['summary'])
            if not x['has_hint'] or not x['has_solution']:
                error('new_exercise_disclosures', name, 'New exercise needs separate hint and solution disclosures', exercise=x['summary'])
            if not (x['id'] or '').startswith('book-'):
                error('new_exercise_id', name, 'New exercise needs a book-prefixed ID', exercise=x['summary'])
        for ident in fragment.ids:
            if not ident.startswith('book-'):
                error('new_anchor_prefix', str(source_path.relative_to(ROOT)), 'New chapter anchor is not book-prefixed', anchor=ident)
        total_new_exercises += len(new_items)
        new_exercise_labels.extend((name,x['summary']) for x in new_items)
        baseline_path = BASELINE/name
        if not baseline_path.exists():
            error('missing_baseline', name, 'Original teaching-page baseline is missing')
            continue
        original = baseline_path.read_text()
        stripped = remove_insertions(doc.source)
        equal = stripped == original
        documented=[c for c in corrections if c['source']=='SafeLearning/'+name]
        restored=stripped
        for c in reversed(documented):
            if restored.count(c['after'])!=1 or original.count(c['before'])!=1:
                error('correction_source_mismatch',name,'Documented mathematical correction is not an exact unique source replacement',line=c['line'])
            else:
                restored=restored.replace(c['after'],c['before'],1)
        reviewed_equal=restored==original
        base_items = exercises(Document(original).root)
        total_baseline_exercises += len(base_items)
        current_items = exercises(doc.root)
        if len(current_items) != len(base_items)+len(new_items):
            error('exercise_count_preservation', name, 'Current exercise count does not equal baseline plus new lab count',
                  baseline=len(base_items), new=len(new_items), current=len(current_items))
        p = dict(file=name, original_sha256=digest(original), stripped_current_sha256=digest(stripped),
                 original_teaching_body_byte_identical=equal)
        if documented:
            p.update(documented_mathematical_corrections=len(documented),
                     documented_corrections_record=str(corrections_path.relative_to(ROOT)),
                     after_reversing_documented_corrections_matches_baseline=reviewed_equal)
        preservation.append(p)
        if not equal and not (documented and reviewed_equal):
            diff = list(difflib.unified_diff(original.splitlines(),stripped.splitlines(),fromfile='baseline/'+name,tofile='stripped-current/'+name,n=1))
            error('original_body_changed', name, 'Original teaching-page source differs after removing only book insertions', diff_excerpt=diff[:35])
        lab_reports.append(dict(file=name, fragment=str(source_path.relative_to(ROOT)),
                                source_sha256=digest(source), source_fragment_current=len(blocks)==1 and blocks[0].strip()==source.strip(),
                                baseline_exercise_counts=counts(base_items), new_exercise_counts=counts(new_items),
                                integrated_exercise_counts=counts(current_items), new_exercises=new_items))

    integrated_labs = sum('book-lab' in p.by_id for p in pages.values())
    if integrated_labs != 21:
        error('lab_count','SafeLearning/','Expected exactly 21 integrated chapter labs',actual=integrated_labs,expected=21)
    passed('Application labs and original teaching-page preservation checked',labs=integrated_labs,teaching_pages=len(preservation))

    # Inspect current authoring documents as well as live targets, so a stale
    # source link cannot hide behind a previously integrated corrected copy.
    for basename in ('case-studies.html','frontmatter.html','glossary.html'):
        path=ROOT/'book'/basename
        source=path.read_text()
        fragment=Document(source)
        integrated_name='book.html' if basename=='frontmatter.html' else basename
        target_doc=pages.get(integrated_name)
        for n in fragment.nodes:
            if n.tag != 'a' or 'href' not in n.attrs:
                continue
            href=n.attrs['href'];split=urlsplit(href)
            if split.scheme or split.netloc:
                continue
            filename=unquote(split.path) or integrated_name
            anchor=unquote(split.fragment)
            dest=fragment if filename==integrated_name else pages.get(filename)
            if dest is None:
                error('source_local_path',str(path.relative_to(ROOT)),'Authoring source links to missing local page',line=n.line,target=href)
            elif anchor and anchor not in dest.by_id:
                error('source_anchor',str(path.relative_to(ROOT)),'Authoring source links to missing anchor',line=n.line,target=href)
        if target_doc is None:
            error('missing_reference_page',integrated_name,'New reference page is missing')
        elif basename != 'frontmatter.html' and source.strip() not in target_doc.source:
            error('stale_reference_fragment',integrated_name,'Integrated reference page differs from its authoritative fragment')
        elif basename == 'frontmatter.html':
            before,marker,after=source.partition('<!-- BOOK CHAPTER CATALOG -->')
            if not marker or before.strip() not in target_doc.source or after.strip() not in target_doc.source:
                error('stale_frontmatter','book.html','Integrated frontmatter does not preserve both authoritative source portions around the generated catalog')
        source_reports.append(dict(file=str(path.relative_to(ROOT)),sha256=digest(source),exercise_counts=counts(exercises(fragment.root))))
    project_items=exercises(Document((ROOT/'book/case-studies.html').read_text()).root)
    if len(project_items)!=9:
        error('project_exercise_count','case-studies.html','Expected nine connected-project exercises',actual=len(project_items),expected=9)
    for x in project_items:
        if not x['level'] or not x['has_hint'] or not x['has_solution']:
            error('project_exercise_structure','case-studies.html','Project exercise lacks level or separate hint/solution',exercise=x['summary'])
    new_exercise_labels.extend(('case-studies.html',x['summary']) for x in project_items)

    try:
        sidebar=sidebar_data((SITE/'components.js').read_text())
        metadata=[m for cluster in sidebar for m in cluster['modules']]
        meta_ids=Counter(m['id'] for m in metadata)
        for ident,n in meta_ids.items():
            if n!=1:
                error('sidebar_duplicate','components.js','Sidebar module ID appears more than once',module=ident)
        by_file={m['file']:m for m in metadata}
        for m in metadata:
            doc=pages.get(m['file'])
            if doc is None:
                error('sidebar_file','components.js','Sidebar links to a missing page',target=m['file'])
                continue
            for section in m.get('sections',[]):
                ident=section['id']
                if ident not in doc.by_id:
                    error('sidebar_anchor','components.js','Sidebar section links to missing anchor',target=m['file']+'#'+ident)
        for c in catalog['chapters']+catalog['references']:
            m=by_file.get(c['file'])
            if m is None:
                error('catalog_sidebar','components.js','Catalog entry has no sidebar entry',target=c['file'])
                continue
            for key in ('id','num','title'):
                if m[key]!=c[key]:
                    error('catalog_sidebar_field','components.js','Sidebar and catalog disagree',target=c['file'],field=key)
            if c['file'] in expected_files:
                ids=[s['id'] for s in m['sections']]
                if ids.count('book-lab')!=1 or ids.index('book-lab')>=ids.index('exercises'):
                    error('sidebar_lab_order','components.js','Sidebar needs one lab entry before exercises',target=c['file'])
            else:
                wanted=[s[0] for s in c['sections']]
                actual=[s['id'] for s in m['sections']]
                if wanted!=actual:
                    error('reference_section_catalog','components.js','Reference sidebar sections differ from catalog',target=c['file'])
        book=pages.get('book.html')
        if book:
            hrefs=[n.attrs.get('href') for n in book.nodes if n.tag=='a']
            for name in expected_files:
                for href in (name,name+'#book-lab'):
                    if href not in hrefs:
                        error('book_catalog_link','book.html','Reading catalog lacks chapter or application link',target=href)
        passed('Sidebar and reading catalog checked',sidebar_entries=len(metadata),catalog_chapters=len(catalog['chapters']),catalog_references=len(catalog['references']))
    except (ValueError,KeyError,subprocess.SubprocessError) as exc:
        error('sidebar_parse','components.js','Could not validate declarative sidebar data',detail=str(exc))

    # These three prior reference pages receive no book additions and should
    # remain exactly preserved. Landing/study-guide additions are intentional.
    untouched=[]
    for name in ('formulas.html','papers.html','open-problems.html'):
        same=pages[name].source==(BASELINE/name).read_text()
        untouched.append(dict(file=name,byte_identical=same))
        if not same:
            error('untouched_reference_changed',name,'Reference page unexpectedly differs from the saved baseline')

    # Label collisions are separate from duplicate HTML IDs; count actual
    # exercise labels across the book, keeping original research labels intact.
    labels=Counter(re.split(r'\s*[—–]\s*',x['summary'],maxsplit=1)[0] for _,x in all_exercises)
    collisions={k:v for k,v in labels.items() if v>1}
    new_collisions={}
    for name,label in new_exercise_labels:
        short=re.split(r'\s*[—–]\s*',label,maxsplit=1)[0]
        if labels[short]>1:
            new_collisions[short]=labels[short]
    if new_collisions:
        warnings.append(dict(category='new_exercise_label_collision',labels=new_collisions,
                             message='New printed exercise label repeats elsewhere in the book.'))

    try:
        idempotence=build_idempotence()
        if not idempotence['current_root_already_matches_build']:
            error('root_rebuild_stale','book/build.py','A fresh build in a disposable copy changes current integrated outputs',
                  changed_files=idempotence['initial_rebuild_changed_files'])
        if not idempotence['repeated_build_is_byte_idempotent']:
            error('build_not_idempotent','book/build.py','Second build in the disposable copy changes outputs',
                  changed_files=idempotence['second_rebuild_changed_files'])
        passed('Build exercised twice in disposable copy',byte_idempotent=idempotence['repeated_build_is_byte_idempotent'])
    except (OSError,subprocess.SubprocessError) as exc:
        idempotence=dict(status='failed to execute disposable build',detail=str(exc))
        error('build_trial_failed','book/build.py','Disposable build could not complete',detail=str(exc))

    # Strong page-level preservation proves more than a count check: every old
    # equation, original exercise, script and section remains byte-identical.
    return dict(status='PASS' if not errors else 'FAIL',
                checked_at_utc=datetime.now(timezone.utc).isoformat(),
                validator='book/validate.py',
                scope='Independent static integration validation; author source files and historical reports are read-only inputs.',
                counts=dict(html_pages=len(pages),expected_html_pages=29,application_labs=integrated_labs,
                            expected_application_labs=21,baseline_teaching_exercises=total_baseline_exercises,
                            new_chapter_exercises=total_new_exercises,new_project_exercises=len(project_items),
                            all_current_exercises=len(all_exercises),all_current_levels=counts([x for _,x in all_exercises]),
                            local_references=local_reference_count),
                checks=checks,errors=errors,warnings=warnings,
                teaching_page_preservation=preservation,untouched_reference_preservation=untouched,
                mathematical_correction_exceptions=dict(enabled=allow_reviewed_corrections,
                    record=str(corrections_path.relative_to(ROOT)) if allow_reviewed_corrections else None,
                    count=len(corrections),scope='Only exact recorded replacements are allowed; all other baseline changes fail.'),
                build_idempotence=idempotence,
                inherited_page_local_exercise_label_reuse=collisions,
                chapter_labs=lab_reports,new_reference_source_documents=source_reports,
                page_source_sha256={name:digest(doc.source) for name,doc in pages.items()},
                limitations=['No browser rendering, KaTeX execution, expanded layout, keyboard interaction or print output was tested.',
                             'External URLs were classified but not fetched; local references in HTML attributes and declarative sidebar metadata were checked.',
                             'This validator does not replace numerical or independent mathematical reviews and makes no new Lean coverage claim.',
                             'Dynamically constructed links beyond the declarative sidebar are not executed.',
                             'Intentional landing and study-guide book navigation additions are outside the exact 21-teaching-page preservation check.'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-only',action='store_true',help='Print the result without writing the review report.')
    parser.add_argument('--output',type=Path,default=REPORT,help='Write a new report without replacing historical evidence.')
    parser.add_argument('--allow-reviewed-corrections',action='store_true',help='Allow only the exact mathematical source replacements recorded in book/coverage/material-corrections.json.')
    args=parser.parse_args()
    args.output=args.output.resolve()
    report=validate(args.allow_reviewed_corrections)
    if not args.check_only:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps(dict(status=report['status'],counts=report['counts'],errors=report['errors'],warnings=report['warnings'],
                          report=None if args.check_only else str(args.output.relative_to(ROOT))),indent=2,ensure_ascii=False))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__':
    sys.exit(main())
