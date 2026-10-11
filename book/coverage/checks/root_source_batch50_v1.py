"""Serialize one independently approved precision correction after frozen20."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, importlib.util, json, shutil, subprocess, sys
R = Path(__file__).resolve().parents[3]
D = R / 'book/coverage/checks/root-source-batch50'
PLAN = D / 'prewrite-plan-v1.json'
CATALOG = R / 'book/coverage/checks/future23-scenario-source50/approved-source50-catalog-v1.json'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
now = lambda: datetime.now(timezone.utc).isoformat()
load = lambda p: json.loads((R / p).read_text())

def write(path, value):
    assert not path.exists(), path
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2)+'\n')

def protect():
    assert load('reports/full-coverage/source49-apply-execution-v1.json')['actual_exit_code'] == 0
    assert H(R/'SafeLearning/cmdp.html') == '5a503475452eacbeb8d5b8f4b3dd846bc3d88ff6817bd900a3cf3b2e2b23f6e9'
    counts = {}
    for n in [21, 22]:
        m = load(f'reports/full-coverage/checkpoint-{n}-manifest.json')
        for name, row in m['proof_files'].items():
            assert H(R/name) == row['sha256'], name
            for path, expected in row['evidence_sha256'].items():
                assert H(R/path) == expected, path
        for name, expected in m['frozen_inputs_sha256'].items():
            assert H(R/m['snapshot']/name) == expected, name
        counts[str(n)] = dict(selected_sources=len(m['proof_files']), frozen_inputs=len(m['frozen_inputs_sha256']), all_hashes_exact=True)
    return counts

def compare(before, after, pages):
    assert before['counts'] == after['counts']
    result = {}
    for section in ['exercises', 'material_source_units']:
        old = {u['key']: u for u in before[section]}
        new = {u['key']: u for u in after[section]}
        assert old.keys() == new.keys()
        result[section] = []
        for key, a in old.items():
            b = new[key]
            assert a.keys() == b.keys()
            for field in a:
                if field not in ['source_sha256', 'source_text', 'text_sha256']:
                    assert a[field] == b[field], (key, field)
            if a['source_text'] != b['source_text']:
                result[section].append(key)
            else:
                assert a['text_sha256'] == b['text_sha256']
            if a['source'] not in pages:
                assert a == b
    return result

if '--apply' not in sys.argv:
    assert H(R/'book/coverage/inventory.json') == '67c800179f90c6d152f5934be9187ad4c4b18275e6cd6678a2b2a2f7ff20ca99'
    registry = load('book/coverage/material-corrections.json')
    assert len(registry['corrections']) == 49
    catalog = load(str(CATALOG.relative_to(R)))
    assert len(catalog['pages']) == 1
    assert not D.exists()
    (D/'simulation/SafeLearning').mkdir(parents=True)
    for p in (R/'SafeLearning').glob('*.html'):
        shutil.copy2(p, D/'simulation/SafeLearning'/p.name)
    sys.path.insert(0, str(R/'book'))
    from validate import Document
    old = load('book/coverage/inventory.json')
    exercise_keys = {u['key'] for u in old['exercises']}
    expected = {section: set() for section in ['exercises', 'material_source_units']}
    pages = []
    for index, item in enumerate(catalog['pages'], 50):
        proposal = load(item['proposal'])
        peer = load(item['independent_review'])
        assert H(R/item['proposal']) == item['proposal_sha256'] == peer['request']['sha256']
        assert peer['errors'] == [] and peer['status'] == 'passed_independent_proposal_only_scenario11_4_precision_semantics_and_two_fresh_full_parsers_future23'
        assert H(R/item['independent_review']) == item['independent_review_sha256']
        assert peer['reviewed_by'] != proposal.get('prepared_by', '/root')
        assert 'approved' in peer['status'] or 'passed' in peer['status']
        source = proposal['source']
        before = (R/source).read_bytes()
        assert H(R/source) == proposal['source_sha256_before']
        after = before
        for rep in proposal['replacements']:
            assert after.count(rep['before'].encode()) == rep.get('count', 1) == 1
            after = after.replace(rep['before'].encode(), rep['after'].encode(), 1)
        target_hash = proposal.get('proposed_source_sha256_after', proposal.get('source_sha256_proposed_after'))
        assert hashlib.sha256(after).hexdigest() == target_hash
        reverse = after
        for rep in reversed(proposal['replacements']):
            assert reverse.count(rep['after'].encode()) == 1
            reverse = reverse.replace(rep['after'].encode(), rep['before'].encode(), 1)
        assert reverse == before and before.count(b'\n') == after.count(b'\n')
        a, b = Document(before.decode()), Document(after.decode())
        assert len(a.nodes) == len(b.nodes)
        assert all((x.tag,x.attrs,x.line) == (y.tag,y.attrs,y.line) for x,y in zip(a.nodes,b.nodes))
        (D/'simulation'/source).write_bytes(after)
        proofs = proposal.get('actual_proof_source_sha256', proposal.get('proof_source_sha256', {}))
        for name, digest in proofs.items():
            assert H(R/name) == digest
        changed = proposal.get('expected_changed_text_keys', [])
        if isinstance(changed, dict):
            assert set(changed) == set(expected)
            for section, keys in changed.items():
                expected[section].update(keys)
        else:
            assert isinstance(changed, list)
            for key in changed:
                expected['exercises' if key in exercise_keys else 'material_source_units'].add(key)
        expected['exercises'].update(proposal.get('expected_changed_exercises', proposal.get('affected_exercise_keys', [])))
        expected['material_source_units'].update(proposal.get('expected_changed_material_units', proposal.get('affected_material_unit_keys', [])))
        pages.append(dict(**item, correction_index=index, source=source,
            before_sha256=H(R/source), after_sha256=target_hash,
            replacements=proposal['replacements'], proof_source_sha256=proofs))
    assert len({p['source'] for p in pages}) == 1
    spec = importlib.util.spec_from_file_location('source48_inventory', R/'book/inventory_claims.py')
    generator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(generator)
    generator.ROOT = D/'simulation'
    generator.OUT = D/'simulation/book/coverage'
    generator.inventory()
    new = json.loads((generator.OUT/'inventory.json').read_text())
    delta = compare(old, new, {p['source'] for p in pages})
    for section in expected:
        assert set(delta[section]) == expected[section], (section, set(delta[section]) ^ expected[section])
    write(PLAN, dict(status='exact_independently_approved_single_page_prewrite_passed', prepared_at_utc=now(),
        writer='/root', catalog=str(CATALOG.relative_to(R)), catalog_sha256=H(CATALOG), pages=pages,
        inventory_before_sha256=H(R/'book/coverage/inventory.json'), registry_before_sha256=H(R/'book/coverage/material-corrections.json'),
        counts=dict(pages=1,replacements=sum(len(p['replacements']) for p in pages),
            changed_exercises=len(delta['exercises']),changed_material_units=len(delta['material_source_units'])),
        changed_text_keys=delta, simulated_inventory=str((generator.OUT/'inventory.json').relative_to(R)),
        simulated_inventory_sha256=H(generator.OUT/'inventory.json'), protection=protect(),
        scope='Exact literal corrections only; no automatic exercise or material correspondence promotion.'))
    print(json.dumps(dict(status='prewrite_passed', plan=str(PLAN.relative_to(R)), counts=load(str(PLAN.relative_to(R)))['counts'])))
else:
    assert load('reports/full-coverage/live-checkpoint-22-attempt1.json')['status'] == 'passed_all31_asset_sha256'
    assert load('reports/full-coverage/pages-checkpoint-22-attempt1.json')['status'] == 'passed'
    plan = json.loads(PLAN.read_text())
    assert plan['writer'] == '/root' and [p['correction_index'] for p in plan['pages']] == [50]
    assert H(CATALOG) == plan['catalog_sha256']
    assert H(R/'book/coverage/inventory.json') == plan['inventory_before_sha256']
    assert H(R/'book/coverage/material-corrections.json') == plan['registry_before_sha256']
    protect()
    for page in plan['pages']:
        assert H(R/page['source']) == page['before_sha256']
        assert H(R/page['proposal']) == page['proposal_sha256']
        assert H(R/page['independent_review']) == page['independent_review_sha256']
        for name, digest in page['proof_source_sha256'].items():
            assert H(R/name) == digest
    history = R/'reports/full-coverage/source-history/approved-scenario-correction50-20261011'
    history.mkdir(parents=True, exist_ok=False)
    names = ['book/coverage/inventory.json','book/coverage/material-corrections.json']
    names += [f'book/coverage/{domain}.json' for domain in ['core','foundations','applied','modules']]
    names += [str(p.relative_to(R)) for p in (R/'book/coverage').glob('*.py')]
    names += [p['source'] for p in plan['pages']]
    preserved = {}
    for name in names:
        target = history/name
        target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copy2(R/name,target)
        assert H(target) == H(R/name)
        preserved[name] = dict(path=str(target.relative_to(R)), sha256=H(target))
    write(history/'preserved-history.json', dict(preserved_at_utc=now(),files=preserved,prewrite_plan_sha256=H(PLAN)))
    registry = load('book/coverage/material-corrections.json')
    assert len(registry['corrections']) == 49
    for page in plan['pages']:
        text = (R/page['source']).read_text()
        original = text
        for rep in page['replacements']:
            assert text.count(rep['before']) == 1
            text = text.replace(rep['before'],rep['after'],1)
        assert hashlib.sha256(text.encode()).hexdigest() == page['after_sha256']
        (R/page['source']).write_text(text)
        registry['corrections'].append(dict(correction_id=page['correction_index'],source=page['source'],
            line=original[:original.index(page['replacements'][0]['before'])].count('\n')+1,
            before_sha256=page['before_sha256'],after_sha256=page['after_sha256'],replacements=page['replacements'],
            reason='Independently approved exact logarithm and exponential expressions with rounding signs and fixed-controller fresh-batch accepted-validation qualification.',
            proposal=page['proposal'],proposal_sha256=page['proposal_sha256'],
            independent_proposal_review=page['independent_review'],independent_proposal_review_sha256=page['independent_review_sha256'],
            root_prewrite_integrity_check=str(PLAN.relative_to(R)),root_prewrite_integrity_check_sha256=H(PLAN),
            authorized_by='User requested all material and Lean verification; root serialized reviewed source corrections after immutable checkpoint22.',
            corrected_at_utc=now(),historical_source=preserved[page['source']]['path'],historical_source_sha256=page['before_sha256'],
            preserved_history=str((history/'preserved-history.json').relative_to(R)),preserved_history_sha256=H(history/'preserved-history.json'),
            status='source_corrected_exact_independently_approved_replacements_pending_fresh_correspondence',
            limits=['Historical execution and review bodies/times preserved; no automatic whole promotion.']))
    (R/'book/coverage/material-corrections.json').write_text(json.dumps(registry,indent=2)+'\n')
    started = now()
    result = subprocess.run([sys.executable,'book/inventory_claims.py'],cwd=R,capture_output=True,text=True)
    write(D/'inventory-generator-execution-v1.json',dict(command=[sys.executable,'book/inventory_claims.py'],
        started_at_utc=started,finished_at_utc=now(),actual_exit_code=result.returncode,stdout=result.stdout,stderr=result.stderr))
    assert result.returncode == 0
    new = load('book/coverage/inventory.json')
    old = json.loads((history/'book/coverage/inventory.json').read_text())
    assert compare(old,new,{p['source'] for p in plan['pages']}) == plan['changed_text_keys']
    simulated = load(plan['simulated_inventory'])
    assert {k:v for k,v in new.items() if k!='generated_at_utc'} == {k:v for k,v in simulated.items() if k!='generated_at_utc'}
    target = R/'book/coverage/inventory-after-correction50.json'
    assert not target.exists()
    shutil.copy2(R/'book/coverage/inventory.json',target)
    write(D/'postwrite-source-integrity-v1.json',dict(status='exact_single_page_source_batch_and_single_final_inventory_passed',
        checked_at_utc=now(),actual_exit_code=0,prewrite_plan_sha256=H(PLAN),counts=plan['counts'],
        changed_text_keys=plan['changed_text_keys'],inventory_after=str(target.relative_to(R)),inventory_after_sha256=H(target),
        registry_after_sha256=H(R/'book/coverage/material-corrections.json'),protection=protect(),
        ledger_state='Current49 review ledgers held pending explicit unchanged-literal identity bindings and fresh changed-source reviews.'))
    print(json.dumps(dict(status='applied',inventory50_sha256=H(target),counts=plan['counts'])))
