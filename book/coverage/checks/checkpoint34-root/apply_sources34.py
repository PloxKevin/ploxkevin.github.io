"""Apply two independently reviewed source packets with fresh inventory parses."""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
INDEX = 'book/coverage/checks/checkpoint33-review/next-unselected-work-index-v1.json'
PEER = 'book/coverage/checks/checkpoint34-review/independent-two-packet-cumulative-review-v1.json'
PEER_SHA = None  # Required CLI fingerprint; finalized independently before execution.
BASE = 'book/coverage/inventory.json'
CORRECTIONS = 'book/coverage/material-corrections.json'
WORK = 'reports/full-coverage/source34-parsers-v1'
HISTORY = 'reports/full-coverage/source-history/checkpoint34-before-corrections89-90-v1'
OUT = 'reports/full-coverage/checkpoint34-source-corrections89-90-v1.json'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def ref(n):
    return dict(file=n, sha256=sha(ROOT / n))


def read(n):
    return json.loads((ROOT / n).read_bytes())


def exact(r):
    assert not Path(r['file']).is_absolute() and '..' not in Path(r['file']).parts
    assert sha(ROOT / r['file']) == r['sha256']
    return ROOT / r['file']


def new(n, data):
    p = ROOT / n
    assert not p.exists() and not p.is_symlink()
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open('xb') as f:
        f.write(data)


def encode(d):
    return (json.dumps(d, indent=2) + '\n').encode()


ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--peer', required=True)
ap.add_argument('--peer-sha256', required=True)
args = ap.parse_args()
PEER, PEER_SHA = args.peer, args.peer_sha256
assert not any((ROOT / n).exists() for n in [WORK, HISTORY, OUT])
assert sha(ROOT / PEER) == PEER_SHA
peer, index, baseline = read(PEER), read(INDEX), read(BASE)
assert peer['status'] == 'passed_independent_current88_exact_NN14_3_and_Conditional387_cumulative_candidate_source_qualification_review_only' and peer['errors'] == []
assert peer['live_site_owner_inventory_or_selected_proof_edits'] is False
assert peer['protection_errors'] == []
exact_candidate_pages = {r['source']: r['candidate'] for r in peer['pages']}
assert set(exact_candidate_pages) == {'SafeLearning/nn-in-the-loop.html', 'SafeLearning/primer-probability.html'}
assert all(r['whole_page_forward_and_inverse_exact'] and r['all_raw_tags_DOM_attributes_lines_and_inline_scripts_exact'] and r['outside_reviewed_wording_exact'] for r in peer['pages'])
assert peer['changed_physical_literal_keys']['exercises'] == ['nn-in-the-loop.html::exercise-17'] and peer['whole_two_page_exact_byte_inverse'] is True
assert peer['all_other27_pages_and_all_other_literal_records_exact_except_required_current_page_fingerprints'] is True
assert peer['Conditional387_whole_decision_conditional_on_exact_application']['approved'] is True
assert peer['current_NN14_3_and_Conditional387_whole_approved_before_source_application'] is False
assert len(read(CORRECTIONS)['corrections']) == 88
assert ref(BASE)['sha256'] == index['current_inventory']['sha256']
packets = []
for task in index['next_tasks'][1:3]:
    exact(task['proposal']); exact(task['narrow_peer']); exact(task['packet'])
    if task['id'] == 'apply_exact_NN14_3_precision_and_select_NN65':
        replacements = [dict(before=r['exact_before_utf8'], after=r['exact_after_utf8']) for r in task['source_qualification']['exact_four_entire_line_changes']]
        source, family = 'SafeLearning/nn-in-the-loop.html', 'NN65'
    else:
        replacements = task['source_qualification']['exact_replacements']
        source, family = 'SafeLearning/primer-probability.html', 'Conditional28'
    packets.append(dict(source=source, replacements=replacements,
                        proposal=task['proposal'], semantic_peer=task['narrow_peer'], family=family))
assert len(packets) == 2 and sum(len(p['replacements']) for p in packets) == 6
selected = read('reports/full-coverage/checkpoint-33-selection.json')
held = {n: r['sha256'] for n, r in selected['proof_files'].items()}
held.update({f'book/coverage/{o}.json': sha(ROOT / f'book/coverage/{o}.json') for o in ['foundations', 'applied', 'modules', 'core', 'applied-promotions']})
site_before = {n: sha(ROOT / n) for n in [*baseline['source_sha256'], 'SafeLearning/style.css', 'SafeLearning/components.js']}
assert all(site_before[n] == h for n, h in baseline['source_sha256'].items())
pages = {n: (ROOT / n).read_bytes() for n in baseline['source_sha256']}
previous = baseline
stages = []
for ordinal, packet in enumerate(packets, 89):
    name = packet['source']
    before = pages[name]
    text = before.decode()
    for replacement in packet['replacements']:
        assert text.count(replacement['before']) == 1 and replacement['after'] not in text
        text = text.replace(replacement['before'], replacement['after'], 1)
    after = text.encode()
    inverse = text
    for replacement in reversed(packet['replacements']):
        assert inverse.count(replacement['after']) == 1
        inverse = inverse.replace(replacement['after'], replacement['before'], 1)
    assert inverse.encode() == before and before.count(b'\n') == after.count(b'\n')
    pages[name] = after
    with tempfile.TemporaryDirectory(prefix=f'checkpoint34-correction{ordinal}-') as td:
        temp = Path(td)
        for n, data in pages.items():
            target = temp / n
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        for n in ['book/inventory_claims.py', 'book/validate.py']:
            target = temp / n
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT / n, target)
        command = ['/usr/bin/python', '-B', '-E', str(temp / 'book/inventory_claims.py')]
        log = WORK + f'/step{ordinal}-parser.log'
        started, tick = datetime.now(timezone.utc).isoformat(), time.monotonic()
        (ROOT / log).parent.mkdir(parents=True, exist_ok=True)
        with (ROOT / log).open('xb') as f:
            r = subprocess.run(command, cwd=temp, stdout=f, stderr=subprocess.STDOUT)
        assert r.returncode == 0
        data = (temp / BASE).read_bytes()
        current = json.loads(data)
        native = dict(status='passed', actual_command=command, actual_workdir=str(temp), actual_exit_code=r.returncode,
                      started_at_utc=started, finished_at_utc=datetime.now(timezone.utc).isoformat(), elapsed_seconds=time.monotonic()-tick,
                      raw_log=ref(log), parser=ref('book/inventory_claims.py'), parser_ROOT_and_OUT_isolated=True,
                      candidate_page_sha256=hashlib.sha256(after).hexdigest())
    assert current['counts'] == previous['counts']
    old_ex, new_ex = {v['key']: v for v in previous['exercises']}, {v['key']: v for v in current['exercises']}
    assert set(old_ex) == set(new_ex)
    changed_exercises = [n for n in old_ex if {k:v for k,v in old_ex[n].items() if k!='source_sha256'} != {k:v for k,v in new_ex[n].items() if k!='source_sha256'}]
    assert set(changed_exercises) == ({'nn-in-the-loop.html::exercise-17'} if packet['family']=='NN65' else set())
    for n in old_ex:
        assert {k:v for k,v in old_ex[n].items() if k not in {'source_sha256','source_text','text_sha256'}} == {k:v for k,v in new_ex[n].items() if k not in {'source_sha256','source_text','text_sha256'}}
    old_units, new_units = [{v['key']: v for v in d['material_source_units']} for d in [previous, current]]
    assert set(old_units) == set(new_units)
    changed = [n for n in old_units if old_units[n]['text_sha256'] != new_units[n]['text_sha256']]
    assert changed and all(old_units[n]['source'] == name for n in changed)
    for n in old_units:
        assert {k: v for k, v in old_units[n].items() if k not in {'source_sha256', 'source_text', 'text_sha256'}} == {k: v for k, v in new_units[n].items() if k not in {'source_sha256', 'source_text', 'text_sha256'}}
    native_name = WORK + f'/step{ordinal}-parser-native.json'
    new(native_name, encode(native))
    stages.append(dict(changed_exercise_keys=changed_exercises, ordinal=ordinal, packet=packet, before=before, after=after, inventory=data, changed_keys=changed, parser=ref(native_name)))
    previous = current
assert all(pages[n] == exact(r).read_bytes() for n, r in exact_candidate_pages.items())
assert all(sha(ROOT / n) == h for n, h in {**held, **site_before}.items())
for n in [BASE, CORRECTIONS, *exact_candidate_pages]:
    new(HISTORY + '/' + n, (ROOT / n).read_bytes())
corrections = read(CORRECTIONS)
original_corrections = list(corrections['corrections'])
applications = []
for stage in stages:
    ordinal, packet = stage['ordinal'], stage['packet']
    name = packet['source']
    assert (ROOT / name).read_bytes() == stage['before']
    prior_name = HISTORY + f'/step{ordinal}-before.html'
    new(prior_name, stage['before'])
    before_inv, after_inv = [f'book/coverage/inventory-{kind}-correction{ordinal}.json' for kind in ['before', 'after']]
    new(before_inv, (ROOT / BASE).read_bytes())
    (ROOT / name).write_bytes(stage['after'])
    (ROOT / BASE).write_bytes(stage['inventory'])
    new(after_inv, stage['inventory'])
    entry = dict(correction_id=ordinal, source=name, before_sha256=hashlib.sha256(stage['before']).hexdigest(),
                 after_sha256=hashlib.sha256(stage['after']).hexdigest(), replacements=packet['replacements'],
                 corrected_at_utc=datetime.now(timezone.utc).isoformat(),
                 status='exact_reviewed_source_correction_owner_identity_and_mapping_rebase_pending',
                 source_proposal=packet['proposal'], independent_semantic_review=packet['semantic_peer'],
                 cumulative_independent_review=ref(PEER), historical_source=ref(prior_name),
                 inventory_before=ref(before_inv), inventory_after=ref(after_inv), actual_fresh_parser=stage['parser'])
    corrections['corrections'].append(entry)
    (ROOT / CORRECTIONS).write_bytes(encode(corrections))
    applications.append(entry)
assert corrections['corrections'][:88] == original_corrections and len(corrections['corrections']) == 90
assert all(sha(ROOT / n) == h for n, h in held.items())
assert all(sha(ROOT / n) == h for n, h in site_before.items() if n not in exact_candidate_pages)
record = dict(status='passed_exact_reviewed_corrections89_90_applied_owner_rebase_pending',
              applications=applications, final_inventory=ref(BASE), source_pages={n: ref(n) for n in exact_candidate_pages},
              independent_cumulative_review=ref(PEER), old_owners_and_selected33_proofs_preserved=True,
              exercises_changed=1, changed_exercise_keys=['nn-in-the-loop.html::exercise-17'], changed_physical_keys=sorted({n for s in stages for n in s['changed_keys']}),
              whole_coverage_or_new_aggregate_claimed=False, coverage_complete=False)
new(OUT, encode(record))
print(json.dumps(dict(status=record['status'], inventory=record['final_inventory'], changed_units=len(record['changed_physical_keys']))))
