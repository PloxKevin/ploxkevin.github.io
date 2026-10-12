"""Apply four independently reviewed narrow corrections after actual delivery28.

Four complete parser runs finish before any source writes. Preserve original
bytes and receipts; owner identities and mathematical promotions are separate.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, importlib.util, json, subprocess, sys

ROOT = Path(__file__).resolve().parents[3]
SELF = 'book/coverage/checks/root_apply_source61_64_v1.py'
CLOSURE = 'book/coverage/checks/future28-core/completed28-content-and-metadata-delivery-closure-v1.json'
CONTRACT = 'book/coverage/checks/future29-core/source61-64-full29-application-contract-v1.json'
REPORT = 'reports/full-coverage/source61-64-corrections-application-v1.json'
HISTORY = 'reports/full-coverage/source-history/approved-corrections61-64-20261011'
PEERS = [
 ('book/coverage/checks/future28-foundations/original-basics-source61-three-actual-countermodels-supplement28-v1/0e5f5209b3f76dade397ad8f9be66f3d0fe459ea62632964fc8ade3391ea2e7e/basics-source61-independent-modules28-closed-v1.json', '0e5f5209b3f76dade397ad8f9be66f3d0fe459ea62632964fc8ade3391ea2e7e'),
 ('book/coverage/checks/future28-core/prospective-source62-independent-modules-v1/optimization-source62-narrow-full-literal-parser-independent-modules28-peer-v1.json', '9c70413a1cbe5b15511bf43aac6b279b36790904c7ae63c058a6de34fe2e9c23'),
 ('book/coverage/checks/future28-foundations/source63-independent-foundations29-v1/source63-narrow-wording-full29-parser-independent-foundations29-peer-v1.json', '0f9bd3f9cfaa04088aadef61621710931ff96e2f27b7e036875f95d753f7a390'),
 ('book/coverage/checks/future28-foundations/source64-exact-norm-uses-qualifiers29-v1/source64-narrow-exact-wording-and-full29-parser-approved-closed-v1.json', '4955705fdf743ab13277ac04cce6f74ff73d7a7e3eeef2d37fea443e7c385520'),
]

def module(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT/path)
    value = importlib.util.module_from_spec(spec); spec.loader.exec_module(value)
    return value

b = module('source61_64_original_parser_guard', 'book/coverage/checks/root_apply_source54_55_v3.py')
d = module('source61_64_original_delivery_guard', 'book/coverage/checks/root_close_publication28_delivery_v2.py')

def path(n):
    p = Path(n) if Path(n).is_absolute() else b.safe(n)
    assert p.is_file() and not p.is_symlink()
    assert p.resolve().is_relative_to(ROOT) or p.resolve().is_relative_to('/tmp')
    return p

def ref(n):
    p = path(n); return {'file': str(n), 'sha256': b.sha(p)}

def checked(r):
    p = path(r['file']); assert b.sha(p) == r['sha256'], r['file']; return p

def original_receipt(r):
    p = checked(r); value = b.read(p)
    assert type(value['actual_exit_code']) is int and value['actual_exit_code'] == 0
    log = value.get('raw_log', value.get('log'))
    row = log if isinstance(log, dict) else {'file':log,'sha256':value.get('raw_log_sha256',value.get('log_sha256'))}
    checked(row)
    return [ref(str(p)), row]

def guards():
    assert Path(__file__).resolve() == ROOT/SELF
    assert b.sha(ROOT/'book/coverage/checks/root_apply_source54_55_v3.py') == '6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
    assert b.sha(ROOT/d.SELF) == '20eaea5fd4714a948a9c7afc52a47bfee5a8853f1c3b5029e34d71f7eafa2a48'
    closure = b.read(path(CLOSURE))
    assert closure['status'] == 'passed_actual_checkpoint28_content_and_metadata_delivery' and closure['coverage_complete'] is False
    for n,h in closure['exact_native_evidence_sha256'].items(): checked({'file':n,'sha256':h})
    assert d.git(['rev-parse','HEAD']).stdout.decode().strip() == closure['metadata_commit']
    assert d.git(['ls-remote','origin','refs/heads/main']).stdout.decode().split() == [closure['metadata_commit'],'refs/heads/main']
    assets = d.immutable()
    assert b.sha(path('book/coverage/inventory.json')) == '6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
    assert b.sha(path('book/coverage/material-corrections.json')) == '90097eba3c8b954074285ee91010745685c5f3e27cc99caf966c76d9ae7a1d81'
    assert len(b.read(path('book/coverage/material-corrections.json'))['corrections']) == 60
    assert not (ROOT/REPORT).exists() and not (ROOT/HISTORY).exists()
    for num in range(61,65):
        assert not (ROOT/f'book/coverage/inventory-before-correction{num}.json').exists()
        assert not (ROOT/f'book/coverage/inventory-after-correction{num}.json').exists()
    return closure, assets

def prepare():
    closure, assets = guards(); assert not (ROOT/CONTRACT).exists()
    peers = []
    for n,h in PEERS:
        checked({'file':n,'sha256':h}); value = b.read(path(n))
        assert value['errors'] == [] and value['status'].startswith('passed_independent_')
        peers.append(value)
    proposal_refs = [peers[0]['reader_decision']['request'], peers[1]['original_author_proposal'], peers[2]['proposal'], peers[3]['proposal']]
    receipt_refs = [peers[0]['actual_reader_execution'], peers[1]['actual_finalizer'], peers[2]['actual_finalizer'], peers[3]['actual_finalizer']]
    assert peers[0]['actual_reader_exit_code'] == 0 and peers[0]['reader_decision']['fresh_exact_changed_text_keys']['exercises'] == []
    assert peers[1]['full_literal_context_three_narrow_qualifiers_approved'] is True and peers[1]['independent_full29_parser_actual_exit_code'] == 0
    assert peers[2]['semantic_decision']['wording_approved'] is True and peers[2]['native_exit_code'] == 0
    assert peers[3]['native_exit_code'] == 0 and all(r['approved'] is True for r in peers[3]['narrow_wording_decisions'])
    evidence = [ref(CLOSURE), ref(SELF)]
    candidates, steps = {}, []; previous = b.read(path('book/coverage/inventory.json'))
    sys.path.insert(0,str(ROOT/'book')); from validate import Document
    for num, pr, rr, peer in zip(range(61,65),proposal_refs,receipt_refs,peers):
        proposal = b.read(checked(pr)); evidence += [pr, *original_receipt(rr), {'file':PEERS[num-61][0],'sha256':PEERS[num-61][1]}]
        source = proposal['source']['file']; original = path(source).read_bytes()
        assert b.sha(path(source)) == proposal['source']['sha256']
        replacements = proposal.get('exact_replacements', [proposal.get('only_replacement')])
        new = original.decode()
        for r in replacements:
            assert new.count(r['before']) == 1 and r['after'] not in new
            new = new.replace(r['before'], r['after'], 1)
        candidate = proposal['proposed_source']; checked(candidate); evidence.append(candidate)
        assert new.encode() == path(candidate['file']).read_bytes() and new.count('\n') == original.decode().count('\n')
        reverse = new
        for r in reversed(replacements):
            assert reverse.count(r['after']) == 1; reverse = reverse.replace(r['after'],r['before'],1)
        assert reverse.encode() == original
        assert [(n.tag,n.attrs,n.line) for n in Document(original.decode()).nodes] == [(n.tag,n.attrs,n.line) for n in Document(new).nodes]
        changed = proposal.get('fresh_parser_changed_text_keys', proposal.get('fresh_changed_literal_keys'))
        step = {'correction_id':num,'source':source,'source_sha256_before':b.sha(path(source)),'proposal':pr,'candidate':candidate,'peer':{'file':PEERS[num-61][0],'sha256':PEERS[num-61][1]},'exact_replacements':replacements,'exact_changed_text_keys':changed,'counts':previous['counts']}
        candidates[source] = new.encode(); data, following = b.full_parser(candidates)
        b.inventory_diff(previous,following,step); previous = following; steps.append(step)
    record = {'status':'prepared_exact_cumulative_source61_to64_full29_application_contract_only','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(SELF),'completed28_delivery':ref(CLOSURE),'metadata_commit':closure['metadata_commit'],'before_inventory':ref('book/coverage/inventory.json'),'before_corrections':ref('book/coverage/material-corrections.json'),'steps':steps,'final_page_sources_sha256':previous['source_sha256'],'original_evidence':evidence,'five_owner28_sha256':{f'book/coverage/{n}.json':b.sha(path(f'book/coverage/{n}.json')) for n in ['core','foundations','applied','modules','applied-promotions']},'all31_source60_assets_sha256':assets,'both_parser_ROOT_and_OUT_isolated':True,'coverage_complete':False}
    guards(); b.write_new(ROOT/CONTRACT,b.encoded(record))
    print(json.dumps({'contract':ref(CONTRACT),'steps':[61,62,63,64],'coverage_complete':False}))

def apply(contract_sha):
    closure, assets = guards(); checked({'file':CONTRACT,'sha256':contract_sha}); contract = b.read(path(CONTRACT))
    assert contract['helper'] == ref(SELF) and contract['completed28_delivery'] == ref(CLOSURE) and contract['metadata_commit'] == closure['metadata_commit']
    checked(contract['before_inventory']); checked(contract['before_corrections'])
    assert [s['correction_id'] for s in contract['steps']] == [61,62,63,64]
    for n,h in contract['five_owner28_sha256'].items(): checked({'file':n,'sha256':h})
    assert contract['all31_source60_assets_sha256'] == assets
    copies = {}; aliases = {}
    originals = ['book/coverage/inventory.json','book/coverage/material-corrections.json',*contract['five_owner28_sha256'],*[s['source'] for s in contract['steps']]]
    for n in originals:
        r = ref(n); target = HISTORY+'/source60-owner28-original/'+n
        assert not (ROOT/target).exists(); copies[target] = r
        aliases[n] = {'file':target,'sha256':r['sha256']}
    for r in [*contract['original_evidence'],ref(CONTRACT)]:
        p = checked(r); target = HISTORY+'/semantic-original-by-sha256/'+r['sha256']+'/'+p.name
        assert not (ROOT/target).exists(); copies[target] = r
        aliases[r['file']] = {'file':target,'sha256':r['sha256']}
    candidates, parsed = {}, []; previous = b.read(path('book/coverage/inventory.json'))
    for step in contract['steps']:
        checked(step['proposal']); checked(step['candidate']); checked(step['peer'])
        assert b.sha(path(step['source'])) == step['source_sha256_before']
        new = path(step['source']).read_text()
        for r in step['exact_replacements']:
            assert new.count(r['before']) == 1 and r['after'] not in new; new = new.replace(r['before'],r['after'],1)
        assert new.encode() == path(step['candidate']['file']).read_bytes()
        candidates[step['source']] = new.encode(); data, following = b.full_parser(candidates)
        changed = b.inventory_diff(previous,following,step); parsed.append((step,new.encode(),data,changed)); previous = following
    assert previous['source_sha256'] == contract['final_page_sources_sha256']
    # Recheck all live bytes after the complete read-only preparation.
    guards()
    for n,r in copies.items(): checked(r); assert not (ROOT/n).exists()
    for n,r in copies.items(): b.write_new(ROOT/n,checked(r).read_bytes()); checked({'file':n,'sha256':r['sha256']})
    history = HISTORY+'/preserved-history-v1.json'
    b.write_new(ROOT/history,b.encoded({'status':'exact_source60_owner28_and_original_semantic_bytes_preserved_before_source61_to64','preserved_at_utc':datetime.now(timezone.utc).isoformat(),'original_byte_aliases':aliases,'completed28_delivery':ref(CLOSURE),'original_bodies_commands_times_and_failed_trials_unchanged':True,'coverage_complete':False}))
    corrections = b.read(path('book/coverage/material-corrections.json')); applications = []
    for step,new,data,changed in parsed:
        num = step['correction_id']; assert len(corrections['corrections']) == num-1
        assert b.sha(path(step['source'])) == step['source_sha256_before']
        before = f'book/coverage/inventory-before-correction{num}.json'; after = f'book/coverage/inventory-after-correction{num}.json'
        b.write_new(ROOT/before,path('book/coverage/inventory.json').read_bytes())
        b.write_new(ROOT/HISTORY/f'material-corrections-before{num}-original.json',path('book/coverage/material-corrections.json').read_bytes())
        applied_at = datetime.now(timezone.utc).isoformat()
        path(step['source']).write_bytes(new); path('book/coverage/inventory.json').write_bytes(data); b.write_new(ROOT/after,data)
        corrections['corrections'].append({'correction_id':num,'source':step['source'],'before_sha256':step['source_sha256_before'],'after_sha256':step['candidate']['sha256'],'replacements':step['exact_replacements'],'corrected_at_utc':applied_at,'status':'source_corrected_exact_independently_reviewed_scope_snippets_owner_identity_rebase_pending','source_proposal':aliases[step['proposal']['file']],'independent_semantic_review':aliases[step['peer']['file']],'preserved_history':b.ref(ROOT/history),'inventory_before':ref(before),'inventory_after':ref(after),'scope':'Only exact independently reviewed literal corrections; no mathematical coverage promotion.'})
        path('book/coverage/material-corrections.json').write_bytes(b.encoded(corrections))
        assert b.sha(path(step['source'])) == step['candidate']['sha256']
        applications.append({'correction_id':num,'applied_at_utc':applied_at,'source_after':ref(step['source']),'inventory_before':ref(before),'inventory_after':ref(after),'exact_changed_text_keys':changed})
    selection = b.read(path('reports/full-coverage/checkpoint-28-selection.json'))
    for n,r in selection['proof_files'].items(): checked({'file':n,'sha256':r['sha256']})
    changed_names = {s['source'] for s in contract['steps']}
    for n,h in assets.items():
        if n not in changed_names: checked({'file':n,'sha256':h})
    for n,h in contract['five_owner28_sha256'].items(): checked({'file':n,'sha256':h})
    assert len(b.read(path('book/coverage/material-corrections.json'))['corrections']) == 64
    record = {'status':'passed_actual_source61_to64_corrections_full29_inventory_owner_identity_rebase_pending','helper':ref(SELF),'contract':ref(CONTRACT),'applications':applications,'preserved_history':ref(history),'completed28_metadata_commit':closure['metadata_commit'],'selected28_proof_sources_unchanged':1186,'other28_book_assets_unchanged':27,'five_installed28_owner_ledgers_unchanged':True,'coverage_complete':False,'scope':'Only source/inventory corrections. Owner rebasing and every whole-mathematics promotion require separate reviewed integration. Original native receipt bodies, commands, times, logs and trial outcomes stay unchanged.'}
    b.write_new(ROOT/REPORT,b.encoded(record)); print(json.dumps({'status':record['status'],'inventory':ref('book/coverage/inventory.json'),'corrections':[61,62,63,64],'coverage_complete':False}))

if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('mode',choices=['prepare','apply']); parser.add_argument('--contract-sha256'); args = parser.parse_args()
    if args.mode == 'prepare': prepare()
    else: assert args.contract_sha256; apply(args.contract_sha256)
