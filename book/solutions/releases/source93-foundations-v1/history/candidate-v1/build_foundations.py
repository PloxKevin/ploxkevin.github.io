"""Prepare/install an exact, reviewable Block 0 expansion from a frozen baseline.

Existing exercise labels, questions, hints, anchors and scripts are retained.
The author fragment is updated separately and must match its integrated copy.
"""
import argparse
from collections import Counter
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(ROOT/'book/solutions'))
import solution_review as h
from solution_release import atomic_copy
from foundation_content import EXERCISES
from solution_expansions import EXTRA, REPLACEMENTS

BASE = 'book/solutions/releases/source93-foundations-v1'
SITE = 'SafeLearning/primer-basics.html'
AUTHOR = 'book/chapters/primer-basics.html'
GROUPS = {
    'warmup': ('mb-warmup', 'Algebra warm-up'),
    'sets': ('mb-sets-logic', 'Sets and logic'),
    'functions': ('mb-functions', 'Functions and fixed points'),
    'proofs': ('mb-proofs', 'Proofs'),
    'sequences': ('mb-sequences', 'Sequences and series'),
    'bounds': ('mb-sup-inf', 'Bounds and extrema'),
    'topology': ('mb-topology', 'Continuity and topology'),
    'rates': ('mb-asymptotics', 'Rates and work budgets'),
}


def frozen(name):
    entry = h.read(BASE+'/baseline-source92/manifest.json')['files'][name]
    assert h.ref(entry['file']) == entry
    return h.path(entry['file']).read_bytes()


def worked(row):
    anchor, topic = GROUPS[row['group']]
    return f'''<details id="mb-extra-{row['code'].lower()}" style="margin-bottom:14px;border:1px solid #d0d8ea;border-radius:6px;overflow:hidden;">
<summary style="padding:12px 16px;background:#f0f4fb;cursor:pointer;font-weight:600;font-size:14px;">Exercise 0.{row['code']} &mdash; {row['level']}: {row['title']}</summary>
<div style="padding:14px 16px;font-size:14px;">
{row['question']}
<p><a href="#{anchor}">Review: {topic}</a></p>
<details style="margin-top:10px;"><summary style="cursor:pointer;color:#2d5fa6;font-weight:600;">Show hint</summary>{row['hint']}</details>
<details style="margin-top:10px;"><summary style="cursor:pointer;color:#2d5fa6;font-weight:600;">Show worked solution</summary><div style="margin-top:8px;padding:10px 14px;background:#f7f9fc;border-left:3px solid #2d5fa6;border-radius:0 4px 4px 0;">
{row['solution']}
</div></details>
</div></details>
'''


def replace_solutions(raw, rows):
    document = h.Document(raw)
    slots = {h.clean(n.child('summary').text()): h.parts(document, n)['solution']
             for n in document.exercises()}
    changes = []
    for row in rows:
        label, ordinal = row['label'], row['ordinal']
        if label not in slots:
            continue
        slot = slots[label]
        assert slot['html'] == row['parts']['solution']['html']
        extra = EXTRA[ordinal]
        inner = REPLACEMENTS.get(ordinal, slot['html'].strip())
        body = '\n'+'\n'.join(s for s in (extra['before'], inner, extra['after']) if s)+'\n'
        span = slot['range']
        changes.append((span['start_byte'], span['end_byte'], body.encode()))
    for start, end, body in sorted(changes, reverse=True):
        raw = raw[:start]+body+raw[end:]
    return raw


def prepare():
    rows = h.read(BASE+'/baseline-source92/exercises.json')['exercises']
    current = replace_solutions(frozen(SITE), rows).decode()
    authored = replace_solutions(frozen(AUTHOR), rows).decode()
    # The application insert is generated from its actual authoring source.
    current, n = re.subn(r'(<!-- BOOK APPLICATION START -->\n).*?(\n<!-- BOOK APPLICATION END -->)',
                        lambda m: m[1]+authored.strip()+m[2], current, flags=re.S)
    assert n == 1

    insertions = []
    for group, (anchor, topic) in GROUPS.items():
        entries = [e for e in EXERCISES if e['group'] == group]
        # Each guided ladder is ordered Easy then Medium, with stable labels.
        entries.sort(key=lambda e: {'Easy': 0, 'Medium': 1, 'Hard': 2}[e['level']])
        prefix = ('<h3 class="subsection-heading" id="mb-practice-warmup">Practice: Algebra warm-up</h3>\n'
                  '<p>Start here if signs, fractions or inequality steps need a refresher. '
                  'Work through the six guided questions before the set exercises.</p>\n') if group == 'warmup' else (
                  '<p><strong>Guided build-up.</strong> Start with these smaller questions to practise '
                  'the tools used by the graded exercises that follow.</p>\n')
        block = ('<!-- FOUNDATION PRACTICE START: '+group+' -->\n'+prefix+
                 ''.join(worked(e) for e in entries)+
                 '<!-- FOUNDATION PRACTICE END: '+group+' -->\n')
        if group == 'warmup':
            marker = '    <!-- ===== SECTION 1: SETS, QUANTIFIERS & LOGIC ===== -->'
            assert current.count(marker) == 1
            current = current.replace(marker, block+'\n'+marker, 1)
        else:
            heading = 'mb-practice-'+{'rates':'asymptotics'}.get(group, group)
            pattern = rf'(<h3 class="subsection-heading" id="{heading}">[^<]*</h3>\n[ \t]*<p>.*?</p>\n)'
            current, n = re.subn(pattern, lambda m: m[1]+block, current, count=1)
            assert n == 1, group
        insertions.append(dict(group=group, exercises=[e['code'] for e in entries], html=block, sha256=h.sha(block.encode())))

    # Record exact intentional prose/navigation changes, separate from answers.
    old = h.Document(frozen(SITE))
    route = next(n for n in old.nodes if n.attrs.get('id') == 'reading-route')
    old_route = old.source[route.start:route.end]
    new_route = '''<div class="insight-box" id="reading-route">
      <div class="box-label">A route through this primer</div>
      <p style="margin:0;">This chapter has <strong>80 exercises with worked solutions</strong>: six algebra warm-ups, 69 local guided and graded questions, four application-lab questions, and seven mixed review problems. Every existing question is retained, and 30 new guided questions build the steps needed to solve them. The worked answers explain substitutions, algebra, proof choices and checks.</p>
      <p style="margin:8px 0 0;">For a first pass, begin with the <a href="#mb-practice-warmup">algebra warm-up</a> if needed. In each section, attempt the guided build-up before the original Easy exercises. Continue to Medium when you can explain the steps with the answer closed. Return to Hard and mixed review after the simpler work feels independent; you can spread the chapter across several study sessions.</p>
      <p style="margin:8px 0 0;">Use a hint after a first attempt. Then compare your reasoning with the full answer, write the reason for each step, close it, and solve the question again. Matching the final value is only one check: also verify the domain, comparison direction and assumptions.</p>
      <p style="margin:8px 0 0;">Jump to <a href="#mb-practice-sets">sets &amp; logic</a>, <a href="#mb-practice-functions">functions &amp; fixed points</a>, <a href="#mb-practice-proofs">proofs</a>, <a href="#mb-practice-sequences">sequences</a>, <a href="#mb-practice-bounds">bounds</a>, <a href="#mb-practice-topology">topology</a>, or <a href="#mb-practice-asymptotics">rates</a>.</p>
    </div>'''
    assert current.count(old_route) == 1
    current = current.replace(old_route, new_route, 1)
    old_toc = '      <a href="#mb-sets-logic">1. Sets, Quantifiers &amp; Logic</a>'
    new_toc = '      <a href="#mb-practice-warmup">Start: Algebra warm-up practice</a>\n'+old_toc
    assert current.count(old_toc) == 1
    current = current.replace(old_toc, new_toc, 1)

    h.put(BASE+'/candidates/'+SITE, current.encode())
    h.put(BASE+'/candidates/'+AUTHOR, authored.encode())
    h.json_put(BASE+'/edit-plan.json', dict(
        source_version='Source93', baseline=h.ref(BASE+'/baseline-source92/manifest.json'),
        preserved_existing_exercises=50, expanded_existing_solutions=50,
        added_guided_exercises=30, new_primer_count=80, new_book_count=586,
        new_exercises=EXERCISES, insertions=insertions,
        prose_replacements=[dict(before=old_route, after=new_route), dict(before=old_toc, after=new_toc)],
        files={name:dict(before_sha256=h.sha(frozen(name)), candidate=h.ref(BASE+'/candidates/'+name))
               for name in (SITE, AUTHOR)},
        authoring_and_review='One author; explicit mathematical self-review and separate arithmetic/browser checks. No new independent agent review is claimed.',
        formal_limit='New and changed worked explanations require new exact correspondence; prior proof counts are not complete coverage credit for this expansion.'))
    print(dict(status='prepared', old_exercises=50, new_exercises=80, expanded_solutions=50))


def check(raw, authored, plan):
    baseline_rows = h.read(BASE+'/baseline-source92/exercises.json')['exercises']
    doc = h.Document(raw)
    nodes = doc.exercises()
    assert len(nodes) == 80
    labels = [h.clean(n.child('summary').text()) for n in nodes]
    assert len(labels) == len(set(labels))
    lookup = {label:n for label,n in zip(labels,nodes)}
    restored = raw
    changes = []
    expanded = []
    for row in baseline_rows:
        node = lookup[row['label']]
        actual, original = h.parts(doc, node), row['parts']
        assert node.attrs.get('id') == row['anchor']
        assert actual['problem']['html'] == original['problem']['html'], row['label']
        assert actual['hints'] == original['hints'] or [x['disclosure']['html'] for x in actual['hints']] == [x['disclosure']['html'] for x in original['hints']]
        assert actual['solution']['sha256'] != original['solution']['sha256'], row['label']
        span = actual['solution']['range']
        changes.append((span['start_byte'],span['end_byte'],original['solution']['html'].encode()))
        expanded.append(dict(label=row['label'], old_ordinal=row['ordinal'],
                             current_ordinal=labels.index(row['label'])+1,
                             before_sha256=original['solution']['sha256'],
                             after_sha256=actual['solution']['sha256']))
    for start,end,old in sorted(changes, reverse=True):
        restored = restored[:start]+old+restored[end:]
    text = restored.decode()
    for ins in plan['insertions']:
        assert text.count(ins['html']) == 1
        text = text.replace(ins['html']+('\n' if ins['group']=='warmup' else ''), '', 1)
    for rep in reversed(plan['prose_replacements']):
        assert text.count(rep['after']) == 1
        text = text.replace(rep['after'],rep['before'],1)
    assert text.encode() == frozen(SITE), 'Unplanned change outside solution bodies, recorded practice blocks and route/TOC'
    old_author = h.Document(frozen(AUTHOR))
    new_author = h.Document(authored)
    assert len(new_author.exercises()) == len(old_author.exercises()) == 4
    spans = []
    for a,b in zip(old_author.exercises(),new_author.exercises()):
        x,y = h.parts(old_author,a),h.parts(new_author,b)
        assert x['problem']['html'] == y['problem']['html']
        assert [v['disclosure']['html'] for v in x['hints']] == [v['disclosure']['html'] for v in y['hints']]
        span = y['solution']['range'];spans.append((span['start_byte'],span['end_byte'],x['solution']['html'].encode()))
    restored_author = authored
    for start,end,old in sorted(spans,reverse=True):
        restored_author = restored_author[:start]+old+restored_author[end:]
    assert restored_author == frozen(AUTHOR)
    integrated = re.search(r'<!-- BOOK APPLICATION START -->\n(.*?)\n<!-- BOOK APPLICATION END -->',raw.decode(),re.S).group(1)
    assert integrated.strip() == authored.decode().strip()
    before = h.Document(frozen(SITE))
    old_scripts = [before.source[n.start:n.end] for n in before.nodes if n.tag=='script']
    new_scripts = [doc.source[n.start:n.end] for n in doc.nodes if n.tag=='script']
    assert old_scripts == new_scripts
    old_ids = [n.attrs['id'] for n in before.nodes if 'id' in n.attrs]
    new_ids = [n.attrs['id'] for n in doc.nodes if 'id' in n.attrs]
    assert set(old_ids) <= set(new_ids) and len(new_ids) == len(set(new_ids))
    for name,ref in h.read(BASE+'/baseline-source92/manifest.json')['files'].items():
        if name.startswith('SafeLearning/') and name != SITE:
            assert h.ref(name) == dict(file=name,sha256=ref['sha256']), name
    return dict(status='passed_exact_expansion_preservation', source_version='Source93',
                old_exercises_preserved=50, solutions_expanded=expanded,
                added_exercises=[e['code'] for e in EXERCISES], primer0_exercises=80,
                scripts_byte_identical=True, other_30_reader_assets_byte_identical=True,
                author_fragment_matches_integrated=True, all_old_anchors_retained=True,
                limitation='Structural preservation is not mathematical or pedagogical approval.')


def install():
    plan = h.read(BASE+'/edit-plan.json')
    data = {name:h.path(info['candidate']['file']).read_bytes() for name,info in plan['files'].items()}
    check(data[SITE],data[AUTHOR],plan)
    for name,info in plan['files'].items():
        assert h.ref(name)['sha256'] in {info['before_sha256'], info['candidate']['sha256']}
        atomic_copy(ROOT/name,data[name])
    result = check(h.path(SITE).read_bytes(),h.path(AUTHOR).read_bytes(),plan)
    result['edit_plan'] = h.ref(BASE+'/edit-plan.json')
    result['files'] = {name:h.ref(name) for name in plan['files']}
    h.json_put(BASE+'/installation.json',result)
    print(dict(status=result['status'], primer0_exercises=80, old_solutions_expanded=50))


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('command', choices=['prepare','check','install'])
    command=parser.parse_args().command
    if command=='prepare':prepare()
    elif command=='install':install()
    else:
        plan=h.read(BASE+'/edit-plan.json')
        result=check(h.path(BASE+'/candidates/'+SITE).read_bytes(),h.path(BASE+'/candidates/'+AUTHOR).read_bytes(),plan)
        h.json_put(BASE+'/preservation-check.json',result)
        print(dict(status=result['status'], primer0_exercises=result['primer0_exercises']))
