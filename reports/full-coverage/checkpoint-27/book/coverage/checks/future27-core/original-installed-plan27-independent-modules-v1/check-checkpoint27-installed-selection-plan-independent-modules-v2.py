from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json,sys,importlib.util,ast
R=Path('/home/oxrexkevin/SafetyBased');P=R/'book/coverage/checks/future27-core/checkpoint27-installed-owner-selection-plan-draft-v1.json';H=R/'book/coverage/prepare_checkpoint27_selection_v2.py';O=Path('/tmp/checkpoint27-installed-selection-plan-independent-modules-check-result-v2.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
def read(p):return json.loads(p.read_bytes())
def checked(r):
 assert set(r)=={'file','sha256'};p=R/r['file'];assert not Path(r['file']).is_absolute() and '..' not in Path(r['file']).parts and p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
assert sha(P)=='d2f99ec31b5e110f0f2ab0a68f5b316b90ca85c2a78dbba35e53e3b7fc80ef92' and sha(H)=='1cdb720a1380e6a36aff457f2587d01123fd8455b1beed35a576dd501605efb9'
plan=read(P);assert plan['status']=='installed_current55_owner27_selection_inputs_awaiting_independent_plan_review' and plan['coverage_complete'] is False
assert len(plan['additional_frozen_inputs'])==915 and len(plan['new_mutable_outer_additional_refs_omitted'])==7
closed={ref(P)['file']:sha(P),ref(H)['file']:sha(H)}
for key in ['inventory','baseline_selection','baseline_manifest','baseline_audit','integration_result','actual_integration_execution','global_integrity','actual_canonical_readiness','independent_selection_helper_review']:
 p=checked(plan[key]);closed[plan[key]['file']]=sha(p)
assert plan['helpers_sha256']['book/coverage/retain_baseline_inputs27_v1.py']=='159d6f53b2a2a05cbc68155d2925a14dc46e90b2d47392ab32c6b822877e2d33'
for n,h in plan['helpers_sha256'].items():assert sha(R/n)==h;closed[n]=h
for n,row in plan['additional_frozen_inputs'].items():
 assert set(row)=={'sha256','scope'} and row['scope']=='immutable_audit_or_local_source_evidence' and row['sha256'] not in plan['excluded_full_external_reference_sha256']
 p=R/n;assert not Path(n).is_absolute() and '..' not in Path(n).parts and Path(n).as_posix()==n and p.resolve().is_relative_to(R)
 assert any(p.resolve().is_relative_to((R/base).resolve()) for base in ['book/coverage','reports/full-coverage/source-history']) and not p.is_symlink() and sha(p)==row['sha256'];closed[n]=row['sha256']
 assert p.suffix in {'.py','.json','.md','.log','.html','.lean','.js','.cjs','.txt','.yml','.olean'}
retainerp=R/'book/coverage/checks/future27-core/checkpoint27-retainer-independent-modules-code-review-v1.json';freezepeerp=R/'book/coverage/checks/future27-core/checkpoint27-freezer-helper-independent-modules-review-v1.json'
for p in [retainerp,freezepeerp]:d=read(p);assert d['status']=='passed' and d['errors']==[];closed[ref(p)['file']]=sha(p)
assert sha(retainerp)=='4aad01dd10e50795d1e864dc65cec7c1846477d21964214eee1c81c84da1438d' and sha(freezepeerp)=='95d2b0a8b1cc1ea02b598d043cbaffcc68ff476d8ed76136b8c13fdc8129e9a5'
ft=ast.parse((R/'book/coverage/freeze_checkpoint27_v2.py').read_text());freezer={'CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS':ast.literal_eval(next(n.value for n in ft.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS' for t in n.targets)))}
base=read(checked(plan['baseline_selection']));combined=base['extra_frozen_inputs']|plan['additional_frozen_inputs']
for n,h in freezer['CHECKPOINT27_EXACT_EXTRA_SUFFIX_EXCEPTIONS'].items():assert combined[n]=={'sha256':h,'scope':'immutable_audit_or_local_source_evidence'} and sha(R/n)==h
integrated=read(checked(plan['integration_result']));replacements={x['destination']:x for x in integrated['exact_replacements']}
for n,h in plan['new_mutable_outer_additional_refs_omitted'].items():
 assert n not in plan['additional_frozen_inputs']
 if n in replacements:assert replacements[n]['before_sha256']==h and sha(R/replacements[n]['original26_byte_copy'])==h
 elif n=='book/coverage/inventory.json':assert h==plan['inventory']['sha256'] and sha(R/n)==h
 else:assert n=='book/coverage/material-corrections.json' and sha(R/n)==h
# Root requested final reviewed plan2 change only status, genuine peer ref and
# the export2 pointer to already fixed export3. Both original helper bytes stay.
export3=R/'book/coverage/export_audit27_v3.py';assert export3.is_file() and sha(export3).startswith('f1f99');closed[ref(export3)['file']]=sha(export3)
required_successor={'status':'independently_reviewed_installed_current55_owner27_selection_plan','replace_helper':{'old':{'file':'book/coverage/export_audit27_v2.py','sha256':plan['helpers_sha256']['book/coverage/export_audit27_v2.py']},'new':ref(export3)},'append_independent_plan_review':'Exact genuinely passed peer file/SHA; no source/owner/evidence authorization or count changes.'}
held={n:sha(R/n) for n in list(replacements)+['book/coverage/inventory.json','book/coverage/material-corrections.json']};assert all(held[n]==r['candidate']['sha256'] for n,r in replacements.items())
# Actual selector functions run read-only; exactly one pending-status field is
# substituted only for the named draft read. No physical plan or output changes.
sys.path.insert(0,str(R/'book/coverage'));spec=importlib.util.spec_from_file_location('independent_selector27_plan_preflight',H);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
original_read=module.read;calls=[]
def isolated_read(name):
 d=original_read(name)
 if name==P.relative_to(R).as_posix():
  assert d==plan;d=copy.deepcopy(d);d['status']=required_successor['status'];calls.append({'file':name,'substituted_field':'status','original_value':plan['status'],'in_memory_value':d['status'],'physical_file_changed':False})
 return d
module.read=isolated_read
def prohibited_retention(*a,**kw):raise AssertionError('prepare(apply=False) attempted producer retention')
module.retain=prohibited_retention
preflight=module.prepare(P.relative_to(R).as_posix(),apply=False)
assert preflight=={'status':'passed_selection_preflight_no_writes','proofs':1175,'new_sources':8,'new_public_declarations':141,'owners':5,'coverage_complete':False} and len(calls)==1
assert not (R/module.DESTINATION).exists() and not (R/module.CONTENT_MAP).exists() and sha(P)=='d2f99ec31b5e110f0f2ab0a68f5b316b90ca85c2a78dbba35e53e3b7fc80ef92'
for n,h in held.items():assert sha(R/n)==h
binding=read(R/integrated['binding_manifest']);closed[integrated['binding_manifest']]=integrated['binding_manifest_sha256']
for row in binding['owners'].values():
 for k in ['candidate','reviewed_offer','final_mapping_peer','actual_finalizer']:p=checked(row[k]);closed[row[k]['file']]=sha(p)
failurep=Path('/tmp/checkpoint27-installed-selection-plan-independent-modules-actual-v1.json');failure=read(failurep);assert type(failure['actual_exit_code']) is int and failure['actual_exit_code']==1 and sha(Path(failure['raw_log']))==failure['raw_log_sha256']
for p in [failurep,Path(failure['raw_log']),Path(failure['checker']['file']),Path(failure['actual_runner']['file'])]:closed[str(p)]=sha(p)
result={'preserved_original_reader1_failure':failure,'reader_delta':'Read exact freezer suffix dictionary through AST literal rather than attempting its imports without module search path; producer/draft untouched. Correct actual wrapper task label in v2.','status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'reviewed_plan':ref(P),'original_physical_plan_status':plan['status'],'selector_helper':ref(H),'helper_sha256':sha(H),'retainer_independent_review':ref(retainerp),'freezer_independent_review':ref(freezepeerp),'exact_actual_read_only_selector_preflight_result':preflight,'controlled_metadata_gate_override':calls,'required_reviewed_successor_plan_delta':required_successor,'additional_frozen_inputs_rehashed':915,'seven_mutable_outer_refs_omitted_with_exact_archive_or_frozen_context_preserved':True,'seven_exact_archive_suffixes_in_final_extra_union':True,'all_baseline_rows_current_owners_sources_imports_claims_actualpairs_and_global_checked_by_actual_prepare':True,'genuine_actual_compiler_pairs':16,'new_sources':8,'new_public_theorem_lemma_exports':141,'selected_sources':1175,'public_theorem_lemma_exports':9644,'actual_production_selector_or_export_or_freeze_claim':False,'closed_evidence_sha256':closed,'scope':'Independent complete concrete pending plan read and native prepare(apply=False). Only named draft status was substituted in memory to exercise guards; physical draft remains pending/unchanged. Approval is conditional on exact new reviewed plan2 status+this genuine peer and export3 ref; no owner, selection/content-map or publication writes.'}
with O.open('x') as f:f.write(json.dumps(result,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(O),'preflight':preflight,'extras':915}))
