"""Apply seven independently reviewed source packets with fresh inventory parses."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import shutil
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[4]
INDEX = 'book/coverage/checks/recovery32/next-batch-source-qualification-index-v1.json'
PEER = 'book/coverage/checks/checkpoint33-review/independent-seven-qualifier-cumulative-review-v1.json'
PEER_SHA = 'a45f2228dc92ad115d00c6dee58ae09ab94b957a32305ea863669c2b617471dd'
BASE = 'book/coverage/inventory.json'
CORRECTIONS = 'book/coverage/material-corrections.json'
WORK = 'reports/full-coverage/source33-parsers-v2'
HISTORY = 'reports/full-coverage/source-history/checkpoint33-before-corrections82-88-v1'
OUT = 'reports/full-coverage/checkpoint33-source-corrections82-88-v1.json'


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


assert not any((ROOT / n).exists() for n in [WORK, HISTORY, OUT])
assert sha(ROOT / PEER) == PEER_SHA
peer, index, baseline = read(PEER), read(INDEX), read(BASE)
assert peer['status'].startswith('approved') and peer['errors'] == []
assert peer['no_exercise_statement_changed'] is True and peer['whole_two_page_exact_byte_inverse'] is True
assert peer['tags_attributes_script_bytes_and_line_counts_unchanged'] is True
assert len(peer['approved_prospective_whole_keys']) == 10
assert len(read(CORRECTIONS)['corrections']) == 81
assert ref(BASE)['sha256'] == index['current_checkpoint']['inventory']['sha256']
packets = []
for row in index['ready_for_exact_source_qualification']:
    exact(row['exact_proposal']); exact(row['narrow_wording_and_parser_peer']); exact(row['whole_prospective_peer'])
    packets.append(dict(source=row['wording_source'], replacements=row['wording_substitutions'],
                        proposal=row['exact_proposal'], semantic_peer=row['narrow_wording_and_parser_peer'], family=row['family']))
planar = index['outstanding_correspondence'][0]
packets.append(dict(source='SafeLearning/primer-linalg.html', replacements=[planar['exact_planned_wording_substitution']],
                    proposal=planar['author_request'], semantic_peer=ref(PEER), family='PlanarQuadratic7'))
assert len(packets) == 7 and sum(len(p['replacements']) for p in packets) == 10
selected = read('reports/full-coverage/checkpoint-32-selection.json')
held = {n: r['sha256'] for n, r in selected['proof_files'].items()}
held.update({f'book/coverage/{o}.json': sha(ROOT / f'book/coverage/{o}.json') for o in ['foundations', 'applied', 'modules', 'core', 'applied-promotions']})
site_before = {n: sha(ROOT / n) for n in [*baseline['source_sha256'], 'SafeLearning/style.css', 'SafeLearning/components.js']}
assert all(site_before[n] == h for n, h in baseline['source_sha256'].items())
pages = {n: (ROOT / n).read_bytes() for n in baseline['source_sha256']}
previous = baseline
stages = []
for ordinal, packet in enumerate(packets, 82):
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
    with tempfile.TemporaryDirectory(prefix=f'checkpoint33-correction{ordinal}-') as td:
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
    assert all({k: v for k, v in old_ex[n].items() if k != 'source_sha256'} == {k: v for k, v in new_ex[n].items() if k != 'source_sha256'} for n in old_ex)
    old_units, new_units = [{v['key']: v for v in d['material_source_units']} for d in [previous, current]]
    assert set(old_units) == set(new_units)
    changed = [n for n in old_units if old_units[n]['text_sha256'] != new_units[n]['text_sha256']]
    assert changed and all(old_units[n]['source'] == name for n in changed)
    for n in old_units:
        assert {k: v for k, v in old_units[n].items() if k not in {'source_sha256', 'source_text', 'text_sha256'}} == {k: v for k, v in new_units[n].items() if k not in {'source_sha256', 'source_text', 'text_sha256'}}
    native_name = WORK + f'/step{ordinal}-parser-native.json'
    new(native_name, encode(native))
    stages.append(dict(ordinal=ordinal, packet=packet, before=before, after=after, inventory=data, changed_keys=changed, parser=ref(native_name)))
    previous = current
assert all(pages[n] == exact(r).read_bytes() for n, r in peer['exact_candidate_pages'].items())
assert all(sha(ROOT / n) == h for n, h in {**held, **site_before}.items())
for n in [BASE, CORRECTIONS, *peer['exact_candidate_pages']]:
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
assert corrections['corrections'][:81] == original_corrections and len(corrections['corrections']) == 88
assert all(sha(ROOT / n) == h for n, h in held.items())
assert all(sha(ROOT / n) == h for n, h in site_before.items() if n not in peer['exact_candidate_pages'])
record = dict(status='passed_exact_reviewed_corrections82_88_applied_owner_rebase_pending',
              applications=applications, final_inventory=ref(BASE), source_pages={n: ref(n) for n in peer['exact_candidate_pages']},
              independent_cumulative_review=ref(PEER), old_owners_and_selected32_proofs_preserved=True,
              exercises_changed=0, changed_physical_keys=sorted({n for s in stages for n in s['changed_keys']}),
              whole_coverage_or_new_aggregate_claimed=False, coverage_complete=False)
new(OUT, encode(record))
print(json.dumps(dict(status=record['status'], inventory=record['final_inventory'], changed_units=len(record['changed_physical_keys']))))
