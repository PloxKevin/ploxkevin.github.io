from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,re
R=Path('/home/oxrexkevin/SafetyBased');REQUEST=Path('/tmp/basics-source61-three-actual-countermodels-review-request28-v1.json');OUT=Path('/tmp/basics-source61-countermodels3-independent-modules28-reader-v1.json')
START=datetime.now(timezone.utc).isoformat()
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def h(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def j(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':h(n)}
def check(r):assert h(r['file'])==r['sha256'];return p(r['file'])
assert h(REQUEST)=='0000639fcc6863443ef1ed75ada0829308ead4bab843329168ec5a0e08004f40'
d=j(REQUEST);src=check(d['proof_source']).read_text();assert src==d['full_proof_source_text']
assert not re.search(r'\b(sorry|admit|axiom)\b',src)
names=['SafeLearning.CompleteFoundationsBasicsDegenerateCountermodels28.'+x for x in re.findall(r'^theorem (\w+)',src,re.M)]
assert names==[x['declaration'] for x in d['component_scopes']] and len(names)==3
assert 'Real.volume_univ' in src and 'volume_euclideanSpace_eq_dirac' in src and 'Subsingleton.elim x 0' in src
for k in ['source61_applied','whole_material_unit_coverage_approved','canonical_installation_or_new_selection_claimed']:assert d[k] is False
inv=j(check(d['current_inventory']));units={u['key']:u for u in inv['material_source_units']}
assert d['entire_current60_literal_records']==[units[k] for k in ['primer-basics.html::node-1029','primer-basics.html::node-1031','primer-basics.html::node-1142']]
assert h('book/coverage/inventory.json')==d['current_inventory']['sha256']=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
check(d['original_independent_narrow_proposal_peer']);check(d['original_narrow_source61_proposal'])
catalog=j(check(d['original_byte_catalog']));aliases=catalog['original_byte_aliases'];assert len(aliases)==13
for original,a in aliases.items():check(a);assert h(original)==a['sha256']
history=[]
for r,code in zip(d['all_three_original_histories'],[1,1,0]):
 n=j(check(r));assert type(n['actual_exit_code']) is int and n['actual_exit_code']==n['actual_runner_exit_code']==code
 assert n['actual_command']==['lake','env','lean',n['source']] and n['actual_workdir']==str(R/'verification/lean')
 assert n['source_unchanged'] is True and n['source_sha256_before']==n['source_sha256_after']==h(aliases[n['source']]['file'])
 assert n['source_snapshot_sha256']==h(aliases[n['source_snapshot']]['file'])==n['source_sha256_before']
 assert n['raw_log_sha256']==h(aliases[n['raw_log']]['file']) and n['protection_errors']==[]
 history.append({'native':r,'actual_exit_code':code,'source_sha256':n['source_sha256_before'],'raw_log_sha256':n['raw_log_sha256'],'started_at_utc':n['started_at_utc'],'finished_at_utc':n['finished_at_utc']})
n=j(check(d['actual_source60_tmp_trial']));assert n['source_sha256_before']==d['proof_source']['sha256'] and check(aliases[n['raw_log']]).read_bytes()==b''
primary=[]
for name in ['Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean','Mathlib/MeasureTheory/Measure/Haar/InnerProductSpace.lean','Mathlib/Topology/Compactness/Compact.lean']:
 q=R/'verification/lean/.lake/packages/mathlib'/name;primary.append(ref(q))
assert 'theorem volume_univ : volume (univ : Set ℝ) = ∞' in p(primary[0]['file']).read_text()
assert 'lemma volume_euclideanSpace_eq_dirac [IsEmpty ι]' in p(primary[1]['file']).read_text()
assert 'theorem isCompact_singleton' in p(primary[2]['file']).read_text()
decisions=[dict(x,approved_component=True,whole_unit_approval=False) for x in d['component_scopes']]
assert not OUT.exists()
result={'status':'passed_independent_three_actual_source61_countermodel_components_only','errors':[],'reader_started_at_utc':START,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'proof_source':d['proof_source'],'entire_three_proof_bodies_and_definitions_read':True,'component_decisions':decisions,'entire_current60_literal_records':d['entire_current60_literal_records'],'primary_used_theorem_context_refs':primary,'all_original_native_failures_and_pass_times_preserved':history,'actual_successful_trial':d['actual_source60_tmp_trial'],'actual_raw_success_log_empty':True,'warning_count':0,'original_narrow_proposal':d['original_narrow_source61_proposal'],'original_narrow_proposal_peer':d['original_independent_narrow_proposal_peer'],'original_proposal_body_time_or_uncompiled_status_relabelled':False,'source61_applied':False,'whole_material_unit_coverage_approved':False,'canonical_installation_or_new_selection_claimed':False,'scope':'Exact zero-normal affine levelset univ/infinite real volume; true canonical Euclidean Fin0 singleton volume1; whole Fin0 space compact. These independently validate only the degenerate witnesses supporting the narrow prospective source qualification. No remaining nullset, essential-supremum or compactness clause is promoted.'}
OUT.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'reader':ref(OUT),'approved_components':3,'whole_units':0}))
