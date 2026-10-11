"""Read-only narrow name/body/canonical-pair binding; no new semantic decisions."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy
ROOT=Path('/home/oxrexkevin/SafetyBased')
READY=ROOT/'book/coverage/checks/modules-future25/temporal/two-source-nine-export-canonical-paired-readiness25-v1.json'
PREP=ROOT/'book/coverage/checks/modules-future25/temporal/canonical-source-and-original-history-preparation-v1.json'
OLD=Path('/tmp/modules-temporal25-independent-foundations-full-component-review-v1.json')
OUT=Path('/tmp/modules-temporal25-canonical-name-body-and-pair-independent-foundations-binding-v1.json')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p),'sha256':sha(p)}
def bind(r):
    p=Path(r['file']);p=p if p.is_absolute() else ROOT/p
    assert sha(p)==r['sha256'],str(p);return p
assert not OUT.exists()
assert sha(READY)=='ece72891d687f9d6ea937121ec59b8477b613526a58708ebe5d4726f8150e578'
assert sha(PREP)=='292d6223e81880103ce818516d8c60369f6235b9e6a617432d9f33da8ec9cd80'
assert sha(OLD)=='3804d30cd063a4e3f681f358d5b70c2d140af689c81069785ff345e97536b810'
r=read(READY);p=read(PREP);old=read(OLD)
assert 'passed' in r['status'] and r['public_export_count']==9 and r['new_source_count']==2
assert ref(PREP)==r['source_preparation']
assert len(r['source_files'])==len(p['source_files'])==2 and r['source_files']==p['source_files']
assert bind(p['original_component_peer']).read_bytes()==OLD.read_bytes()
originals={}
for n,a in p['original_path_exact_byte_aliases'].items():
    cp=bind(a['canonical_exact_byte_copy']);orig=Path(n)
    assert orig.read_bytes()==cp.read_bytes() and cp.stat().st_size==a['size_bytes'],n
    originals[n]=a['canonical_exact_byte_copy']
assert len(originals)==43
for k in ['original_component_peer','original_whole_answer_b_peer','original_selected_universal_monotonicity_supplement']:
    assert r[k]==p[k];bind(r[k])
oldfirst=Path('/tmp/modules-doubly-hyperdominant24-trial6.lean').read_text()
oldsecond=Path('/tmp/modules-temporal-diagonal24-trial2.lean').read_text()
assert oldsecond.startswith(oldfirst)
rename={'SafeLearning.CompleteModulesNNDoublyHyperdominant24':'SafeLearning.CompleteModulesNNDoublyHyperdominant25',
        'SafeLearning.CompleteModulesNNTemporalDiagonal24':'SafeLearning.CompleteModulesNNTemporalDiagonal25'}
def renamed(s):
    for a,b in rename.items():s=s.replace(a,b)
    return s
assert p['source_files'][0]['original_source_body']==oldfirst
assert p['source_files'][1]['original_source_body']==oldsecond[len(oldfirst):]
names=[];source_rows=[]
for i,x in enumerate(p['source_files']):
    src=bind(x['source']);snap=bind(x['source_snapshot']);text=src.read_text();assert src.read_bytes()==snap.read_bytes()
    if i==0:assert text==renamed(oldfirst)
    else:
        header='import SafeLearning.CompleteModulesNNDoublyHyperdominant25\n\nset_option autoImplicit false\nset_option relaxedAutoImplicit false\nset_option maxHeartbeats 1200000\nnoncomputable section\nopen Matrix Set\nopen scoped BigOperators\n'
        assert text.startswith(header)
        assert text[len(header):].strip('\n')==renamed(oldsecond[len(oldfirst):]).strip('\n')
    namespace=re.search(r'^namespace (\S+)',text,re.M)[1]
    public=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
    assert public==x['public_theorems'] and len(public)==[6,3][i]
    assert not re.search(r'\b(sorry|admit|axiom)\b',text)
    names+=public
    source_rows.append({'canonical_source':x['source'],'source_snapshot':x['source_snapshot'],
                        'public_theorem_names':public,'original_namespace':list(rename)[i],
                        'new_namespace':namespace,'all_original_statement_and_proof_bodies_exact_after_named_alias_substitution':True})
assert len(names)==len(set(names))==9
oldnames=[re.sub(r'25(?=\.)','24',n) for n in names]
name_map=dict(zip(oldnames,names))
pair_rows=[];modes={x['canonical_source']['file']:set() for x in source_rows}
assert len(r['actual_paired_records'])==4
for x in r['actual_paired_records']:
    rp=bind(x['actual_record']);a=read(rp);log=bind(x['raw_log']);snapshot=bind(x['source_snapshot']);src=bind(x['source'])
    assert x['actual_exit_code']==0 and a['status']=='passed'
    exits=[a[k] for k in ['actual_exit_code','exit_code'] if k in a];assert exits and all(type(v)is int and v==0 for v in exits)
    expected=['lake','env','lean','SafeLearning/'+src.name] if x['kind']=='standalone' else ['lake','build','SafeLearning.'+src.stem]
    commands=[a[k] for k in ['command','actual_command'] if k in a];assert commands and all(c==expected for c in commands)
    assert a['actual_workdir']==str(ROOT/'verification/lean')
    assert a['source']==src.relative_to(ROOT).as_posix() and a['source_sha256_before']==a['source_sha256_after']==sha(src)==sha(snapshot)
    assert a['source_snapshot']==snapshot.relative_to(ROOT).as_posix() and a['source_snapshot_sha256']==sha(snapshot)
    logs=[a[k] for k in ['log','raw_log'] if k in a];assert logs and all(n==log.relative_to(ROOT).as_posix() for n in logs)
    digests=[a[k] for k in ['log_sha256','raw_log_sha256','original_log_sha256'] if k in a];assert digests and all(d==sha(log) for d in digests)
    assert sha(ROOT/a['actual_runner'])==a['actual_runner_sha256']
    assert a['started_at_utc']<a['finished_at_utc'] and a['elapsed_seconds']>0
    if x['kind']=='standalone':assert log.stat().st_size==0
    modes[x['source']['file']].add(x['kind'])
    pair_rows.append({'reference':x['actual_record'],'raw_log':x['raw_log'],'source_snapshot':x['source_snapshot'],
                      'entire_original_actual_record_body_and_time':a,'actual_exit_code':0,'scope':'Genuine canonical compiler execution, original record/time/raw bytes unchanged.'})
assert all(v=={'standalone','named-build'} for v in modes.values())
m=read(ROOT/'reports/full-coverage/checkpoint-24-manifest.json')
assert len(m['proof_files'])==1144
for n,d in m['proof_files'].items():assert sha(ROOT/n)==sha(ROOT/'reports/full-coverage/checkpoint-24'/n)==d['sha256'],n
assets={n:d for n,d in m['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,d in assets.items():assert sha(ROOT/n)==sha(ROOT/'reports/full-coverage/checkpoint-24'/n)==d,n
owners={n:m['working_inputs_sha256'][n] for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json','book/coverage/inventory.json']}
for n,d in owners.items():assert sha(ROOT/n)==d,n
assert old['precise_component_count']==3 and old['errors']==[] and 'passed' in old['status']
scope_rows=copy.deepcopy(old['material_units'])
out={'status':'independent_temporal25_canonical_namespace_body_and_actual_pair_binding_passed','errors':[],
     'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewer':'/root/config21_next',
     'canonical_readiness':ref(READY),'canonical_preparation':ref(PREP),'original_component_peer':ref(OLD),
     'entire_original_component_peer_body_and_time':old,'original_precise_component_rows_and_hypotheses_unchanged':scope_rows,
     'old_to_new_public_declaration_names':name_map,'canonical_sources':source_rows,'source_count':2,'public_export_count':9,
     'all_four_genuine_canonical_paired_records':pair_rows,'all43_original_TMP_byte_aliases':originals,
     'all1144_selected24_sources_and_frozen_copies_exact':True,'all31_current52_assets_and_frozen_copies_exact':True,
     'current24_owner_inventory_sha256':owners,'original_whole_answer_b_peer':r['original_whole_answer_b_peer'],
     'original_selected_monotonicity_evidence_supplement':r['original_selected_universal_monotonicity_supplement'],
     'preserved_original_reader_failure':{'reason':'Own reader accessed source instead of canonical_source in its normalized source summary; sources, statements and namespace transformations had already checked exact. Corrected reader only, originals unchanged.','actual_record':ref(Path('/tmp/modules-temporal25-canonical-binding-independent-foundations-actual-v1.json')),'entire_original_failed_actual_body_and_time':read(Path('/tmp/modules-temporal25-canonical-binding-independent-foundations-actual-v1.json')),'original_checker':ref(Path('/tmp/check-modules-temporal25-canonical-bindings-independent-foundations-v1.py')),'raw_log':ref(Path('/tmp/modules-temporal25-canonical-binding-independent-foundations-actual-v1.log')),'actual_runner':ref(Path('/tmp/run-modules-temporal25-canonical-bindings-independent-foundations-v1.py'))},
     'actual_read_only_checker':ref(Path(__file__)),
     'fresh_semantic_decision_made':False,'whole_c_or_exercise_approved':False,
     'scope':'Narrow genuine canonical name/body/source/snapshot/pair binding only. The entire original three component decisions, reasons, hypotheses, pending FIR realization/loop-transformation/cross-channel/odd/whole-c clauses and times remain unchanged. No new theorem compile, live candidate mapping, current owner or checkpoint24 amendment performed by this checker.'}
with OUT.open('x') as f:json.dump(out,f,indent=2);f.write('\n')
print(json.dumps({'status':'passed','output':ref(OUT),'public_export_count':9,'actual_pair_record_count':4}))
