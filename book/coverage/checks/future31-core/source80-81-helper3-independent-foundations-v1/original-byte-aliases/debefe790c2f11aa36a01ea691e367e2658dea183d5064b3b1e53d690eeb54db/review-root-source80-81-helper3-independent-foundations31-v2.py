from pathlib import Path
import ast, hashlib, json, re, sys
sys.dont_write_bytecode = True
ROOT = Path('/home/oxrexkevin/SafetyBased')
SELF = ROOT/'book/coverage/checks/root_apply_source80_81_v3.py'
EXPECTED = '9162ff607372aafdf3061beb1f44434b9b886ea55e61b067f01f53397f5d5a1b'
OUT = Path('/tmp/root-source80-81-helper3-independent-foundations31-semantic-v2.json')
assert not OUT.exists()
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def path(n): return Path(n) if Path(n).is_absolute() else ROOT/n
def ref(p):
    p = path(p)
    return {'file': str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p), 'sha256': sha(p), 'bytes': p.stat().st_size}
def checked(r):
    p=path(r['file']); assert sha(p)==r['sha256'], r['file']
    if 'bytes' in r: assert p.stat().st_size==r['bytes']
    return p
def read(p): return json.loads(path(p).read_bytes())
assert sha(SELF)==EXPECTED
source=SELF.read_text(); tree=ast.parse(source)
constants={}
for n in tree.body:
    if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name):
        try: constants[n.targets[0].id]=ast.literal_eval(n.value)
        except (ValueError,TypeError): pass
constants['PEER_PINS']={constants['SPECTRAL']:'85db76bb3e923124010b8b25d48d4878cca570243fe74d6df227b24a47e1a2d9',constants['INTEGRAL']:'e008dc4fc6b68ea9abf47f4452f99d57892225d0d42b70b2b85d436549fc44be'}
assert constants['SELF']==str(SELF.relative_to(ROOT))
assert constants['BASE_SHA']=='6b4c52ce05d8ed940a22982107b2ba708dc0f6f28e1a60ab4396b78c68286be0'
assert sha(path(constants['BASE']))==constants['BASE_SHA']
base=path(constants['BASE']).read_text(); ast.parse(base)
evidence=[ref(SELF),ref(constants['BASE'])]
for old in ['/tmp/review-root-source80-81-helper3-independent-foundations31-v1.py','/tmp/run-review-root-source80-81-helper3-independent-foundations31-v1.py','/tmp/root-source80-81-helper3-independent-foundations31-actual-v1.json','/tmp/root-source80-81-helper3-independent-foundations31-actual-v1.log']: evidence.append(ref(old))
for version in [1,2]: evidence.append(ref(f'book/coverage/checks/root_apply_source80_81_v{version}.py'))
sys.path.insert(0,str(ROOT/'book'))
from validate import Document
candidate_rows=[]
for number,live,peername,replacementkey,candidatekey,changedkey in [
    (80,'SafeLearning/primer-linalg.html',constants['SPECTRAL'],'exact_literal_substitutions','prospective_source','actual_changed_literal_keys'),
    (81,'SafeLearning/nn-in-the-loop.html',constants['INTEGRAL'],'exact_replacements','proposed_source','fresh_changed_literal_keys')]:
    p=path(peername); assert sha(p)==constants['PEER_PINS'][peername]
    peer=read(p); assert peer['status'].startswith('passed') and peer['errors']==[]
    nativep=checked(peer['actual_finalizer']); native=read(nativep)
    assert native['status'].startswith('passed') and type(native['actual_exit_code']) is int and native['actual_exit_code']==0
    assert native['helper_sha256_before']==native['helper_sha256_after']
    assert native.get('protection_errors',[])==[] and native['elapsed_seconds']>0
    raw=path(native.get('raw_log',native.get('log')))
    assert sha(raw)==native.get('raw_log_sha256',native.get('log_sha256'))
    for name,digest in native['helper_sha256_before'].items(): assert sha(path(name))==digest
    requestp=checked(peer['request']); request=read(requestp)
    originalp=checked(request['source']); original=path(live).read_bytes()
    assert originalp.read_bytes()==original
    proposedp=checked(request[candidatekey]); proposed=original.decode()
    replacements=request[replacementkey]
    for row in replacements:
        assert proposed.count(row['before'])==1 and row['after'] not in proposed
        proposed=proposed.replace(row['before'],row['after'],1)
    assert proposed.encode()==proposedp.read_bytes()
    reverse=proposed
    for row in reversed(replacements):
        assert reverse.count(row['after'])==1
        reverse=reverse.replace(row['after'],row['before'],1)
    assert reverse.encode()==original and proposed.count('\n')==original.count(b'\n')
    before=Document(original.decode()); after=Document(proposed)
    assert [(n.tag,n.attrs,n.line) for n in before.nodes]==[(n.tag,n.attrs,n.line) for n in after.nodes]
    a=re.findall(rb'<!-- BOOK APPLICATION START -->\n(.*?)\n<!-- BOOK APPLICATION END -->',original,re.S)
    z=re.findall(rb'<!-- BOOK APPLICATION START -->\n(.*?)\n<!-- BOOK APPLICATION END -->',proposed.encode(),re.S)
    assert len(a)==len(z)==1 and a==z
    if number==81: assert a[0]==path(constants['FRAGMENT']).read_bytes().strip()
    if number==80:
        assert peer['full_exact_qualifier_mathematical_correspondence_approved'] is True
        assert request[changedkey]=={'exercises':[],'material_source_units':['primer-linalg.html::node-421']}
    else:
        assert peer['full_current_and_proposed_literals_and_contexts_read'] is True
        assert peer['independent_parser']['both_ROOT_and_OUT_strictly_TMP'] is True
        assert request[changedkey]=={'exercises':['nn-in-the-loop.html::exercise-19'],'material_source_units':['nn-in-the-loop.html::node-1247']}
    assert peer['exact_forward_and_inverse'] is True
    candidate_rows.append({'number':number,'peer':ref(p),'request':ref(requestp),'source':ref(originalp),'proposed':ref(proposedp),'native':ref(nativep),'raw':ref(raw),'exact_replacements':replacements,'changed_keys':request[changedkey],'original_native_elapsed_seconds':native['elapsed_seconds']})
    evidence.extend([ref(p),ref(requestp),ref(originalp),ref(proposedp),ref(nativep),ref(raw)])
deliveryp=path('reports/full-coverage/publication30-finish-root-v1.json');delivery=read(deliveryp)
assert delivery['status']=='passed_actual_checkpoint30_content_and_metadata_push_Pages_all31_delivery'
assert delivery['metadata_commit']==constants['METADATA'] and delivery['coverage_complete'] is False
evidence.append(ref(deliveryp))
for r in delivery['evidence']:
    p=checked(r);evidence.append(ref(p))
    if p.suffix=='.json':
        d=read(p)
        for k in ['actual_exit_code','exit_code']:
            if k in d: assert type(d[k]) is int and d[k]==0
        if 'log' in d:
            assert sha(path(d['log']))==d['log_sha256']
for stem,commit in [('2',delivery['content_commit']),('3',delivery['metadata_commit'])]:
    live=read(f'reports/full-coverage/live-checkpoint-30-attempt{stem}.json')
    pages=read(f'reports/full-coverage/pages-checkpoint-30-attempt{stem}.json')
    assert live['status']=='passed_all31_asset_sha256' and live['commit']==live['remote_main']==commit
    assert pages['status']=='passed' and pages['commit']==pages['expected_commit']==commit
for version,expectedcode in [(1,1),(2,0)]:
    p=path(f'reports/full-coverage/source80-81-readonly-preflight-execution-v{version}.json')
    n=read(p);assert n['actual_exit_code']==expectedcode
    assert sha(path(n['log']))==n['log_sha256']
    evidence.extend([ref(p),ref(n['log'])])
assert "changed_paths = {INVENTORY, CORRECTIONS, *(r['source'] for r in rows)}" in source
assert "actual_corrections[:79] == read(path(HISTORY+'/'+CORRECTIONS))['corrections']" in source
assert "actual_corrections[-2:] == applications" in source
assert "path(INVENTORY).read_bytes() == parsed[-1][1] == path('book/coverage/inventory-after-correction81.json').read_bytes()" in source
assert source.index('if not args.apply:') < source.index('for n in [INVENTORY, CORRECTIONS,')
assert source.index('assert guard() == held') < source.index('for n in [INVENTORY, CORRECTIONS,')
assert "peer['reviewed_helper'] == ref(SELF)" in source
assert "module.ROOT=isolated;module.OUT=isolated/'book/coverage';module.inventory()" in base
assert "assert changed[field]==step['exact_changed_text_keys'][field]" in base
assessment={
    'entire_code_and_pinned_parser_inventory_diff_read':True,
    'default_readonly_two_cumulative_fresh_full29_parsers_before_mutations':True,
    'exact_original79_inventory_corrections_context_1242_31_raw5_guarded':True,
    'exact_two_proposals_peers_genuine_native_logs_and_body_times_verified':True,
    'same_DOM_tags_attrs_lines_and_exact_forward_inverse_verified_independently':True,
    'both_application_blocks_and_NN_fragment_unchanged':True,
    'prewrite_collisions_guard_and_exact_source_inventory_change_domains_read':True,
    'apply_requires_exact_helper_full_code_peer':True,
    'version2_application_only_postwrite_stale_guard_defect_repaired_in3':True,
    'original79_correction_bodies_and_only80_81_newentries_validated_after_write':True,
    'original_v1_native_failure_v2_unexecuted_application_defect_preserved':True,
    'producer_parser_compiler_owner_source_or_publication_invoked_by_reviewer':False,
    'whole_coverage_or_actual_source_application_approved_by_this_code_peer':False,
}
OUT.write_text(json.dumps({'status':'passed_independent_full_source80_81_helper3_code_and_actual_input_schema_review','errors':[],'full_code_read':True,'reviewed_helper':ref(SELF),'candidate_association':candidate_rows,'full_code_assessment':assessment,'direct_evidence':evidence,'coverage_complete':False},indent=2)+'\n')
print(json.dumps({'status':'passed','errors':[],'full_code_read':True,'reviewed_helper':ref(SELF),'candidate_count':len(candidate_rows),'direct_evidence_count':len(evidence)}))
