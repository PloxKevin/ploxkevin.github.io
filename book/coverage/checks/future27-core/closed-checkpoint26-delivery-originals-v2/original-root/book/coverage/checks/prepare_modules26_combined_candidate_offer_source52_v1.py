"""Close NEW isolated Module26 draft offer using actual candidate/pair outputs."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re,copy
R=Path(__file__).resolve().parents[3];B='book/coverage/checks/modules-future26/source52';H=lambda n:hashlib.sha256((R/n).read_bytes()).hexdigest();J=lambda n:json.loads((R/n).read_text());ref=lambda n:{'file':n,'sha256':H(n)}
C=B+'/modules26-combined-candidate-source52-v1.json';I=B+'/modules26-combined-source52-input-bindings-v1.json';G=B+'/modules26-combined-source52-candidate-integrity-v1.json';ACT=B+'/modules26-combined-isolated-candidate-builder-actual-v1.json';OUT=B+'/modules-audit26-candidate-source52-additions-draft-v1.json'
def zero(d):
 v=[d[k]for k in['actual_exit_code','exit_code']if k in d];assert v and all(type(x)is int and x==0 for x in v)
c=J(C);i=J(I);g=J(G);a=J(ACT);zero(a);assert g['candidate']==ref(C)and g['input_bindings']==ref(I);assert H(a['helper'])==a['helper_sha256_before']==a['helper_sha256_after']and H(a['raw_log'])==a['raw_log_sha256']
x=c['reviewed_work_integration26_combined_candidate'];land=c['reviewed_work_integration26_landscape_candidate'];own=x['Module_owned_new_proofs'];cross=x['explicit_cross_owner_required_proofs'];assert len(own)==2 and sum(len(r['declarations'])for r in own.values())==48 and len(cross)==1 and sum(len(r['declarations'])for r in cross.values())==8
assert H('book/coverage/modules.json')==x['baseline25_module_ledger']['sha256'];assert H('book/coverage/inventory.json')==x['current_inventory']['sha256'];s=J('reports/full-coverage/checkpoint-25-selection.json');assert len(s['proof_files'])==1156
required={C:H(C),I:H(I),G:H(G),ACT:H(ACT),a['raw_log']:H(a['raw_log']),a['helper']:H(a['helper'])}
# Every completed native, original semantic, pass/failure and parser/reader byte in
# these unique26 archives remains an explicit frozen input. No live path or open
# finalizer log is captured merely because it will exist later.
for folder in ['book/coverage/checks/modules-future26/landscape','book/coverage/checks/modules-future26/smoothing']:
 for p in (R/folder).rglob('*'):
  if p.is_file()and p.suffix in{'.py','.json','.log','.lean','.txt'}:
   n=p.relative_to(R).as_posix();required[n]=H(n)
for n in ['book/coverage/build_modules26_landscape_candidate_source52_v1.py','book/coverage/build_modules26_landscape_candidate_source52_v2.py','book/coverage/build_modules26_landscape_candidate_source52_v3.py','book/coverage/checks/run_modules_smoothing44_canonical_pair26_v1.py','book/coverage/checks/run_modules_smoothing44_canonical_pair26_v2.py']:
 required[n]=H(n)
# Close the shared measured-runner original by exact bytes without changing the
# native actual records' original absolute path or invocation/time fields.
original=Path(a['actual_runner']['file']);alias=R/B/'original-preparation-runner-v1'/original.name;alias.parent.mkdir(parents=True,exist_ok=True)
if alias.exists():assert hashlib.sha256(alias.read_bytes()).hexdigest()==a['actual_runner']['sha256']
else:alias.write_bytes(original.read_bytes())
assert hashlib.sha256(alias.read_bytes()).hexdigest()==a['actual_runner']['sha256'];required[alias.relative_to(R).as_posix()]=a['actual_runner']['sha256']
for n,row in own.items():
 assert H(n)==row['sha256']
 for p,h in row['evidence_sha256'].items():assert H(p)==h;required[p]=h
for n,row in cross.items():
 required[row['proof_offer']['file']]=row['proof_offer']['sha256']
 for p,h in row['proof_metadata']['evidence_sha256'].items():assert H(p)==h;required[p]=h
reused=land['selected25_reused_source_rows']
for n,row in reused.items():
 assert H(n)==row['sha256']==s['proof_files'][n]['sha256']
 for p,h in row['evidence_sha256'].items():assert H(p)==h;required[p]=h
allowed=set(s['proof_files'])|set(own)|set(cross);dependencies={}
def close(n):
 for importname in re.findall(r'^import\s+(SafeLearning\.\S+)',(R/n).read_text(),re.M):
  p='verification/lean/'+importname.replace('.','/')+'.lean';assert p in allowed,p
  if p not in dependencies:dependencies[p]=H(p);close(p)
for n in own:close(n)
for n,row in cross.items():close(n)
for n,h in x['current_inventory'].items():pass
semantics=[land['original_whole_review'],land['physical_unit_supplement'],x['original_smoothing_whole_review']]
for r in semantics:assert H(r['file'])==r['sha256'];required[r['file']]=r['sha256']
for n,h in required.items():assert H(n)==h,n
body={'schema_version':1,'status':'actual_isolated_module26_candidate_ready_for_independent_final_mechanics','created_at_utc':datetime.now(timezone.utc).isoformat(),'current_inventory':x['current_inventory']['file'],'current_inventory_sha256':x['current_inventory']['sha256'],'module_ledger':C,'module_ledger_sha256':H(C),'mapped_ledger':C,'mapped_ledger_sha256':H(C),'module_builder':a['helper'],'module_builder_sha256':H(a['helper']),'actual_builder':ref(ACT),'actual_builder_raw_log':ref(a['raw_log']),'actual_isolated_candidate_preparation':ref(ACT),'proof_files':own,'proof_selection_owner':'Modules26','new_proof_file_count':2,'new_theorem_or_lemma_count':48,'explicit_cross_owner_required_proofs':cross,'cross_owner_proof_offer_references':[v['proof_offer']for v in cross.values()],'baseline25_module_ledger':x['baseline25_module_ledger'],'base_selection':'reports/full-coverage/checkpoint-25-selection.json','base_selection_sha256':H('reports/full-coverage/checkpoint-25-selection.json'),'actual_passing_baseline_audit':'reports/full-coverage/lean-checkpoint-25/verification-original.json','actual_passing_baseline_audit_sha256':H('reports/full-coverage/lean-checkpoint-25/verification-original.json'),'candidate_input_bindings':ref(I),'candidate_binding_integrity':ref(G),'source_sha256':c['source_sha256'],'original_full_or_precise_source_reviews':semantics,'smoothing_canonical_original_body_binding_peer_pending':True,'fresh_whole_exercise_keys':x['fresh_whole_exercise_keys'],'fresh_whole_material_unit_keys':x['fresh_physical_unit_keys'],'reused_selected25_proof_sources_sha256':{n:r['sha256']for n,r in reused.items()},'required_external_import_dependencies':dependencies,'required_evidence_artifacts_sha256':required,'additional_frozen_inputs':copy.deepcopy(required),'counts':c['counts'],'independent_final_candidate_mapping_peer_pending':True,'live_owner_assets_mutated':False,'coverage_complete':False,'scope_limits':['Two complete current52 whole exercises and nine independently complete physical literals; exact original reviews/reasons/hypotheses/time preserved.','Modules selects only Wind4 and cumulative44 Gaussian classifier proof sources; Applied supplies cumulativeCVaR8 through its explicit reviewed offer. Older quantile1/source37/prefix trials are unselected historical evidence.','Gaussian ideal classifier proof covers deterministic and fixed-independent-seed randomized base classifiers; valid sampling confidence is the given probability-bound premise. All perturbation balls are strict.','Existing selected25 proofs may enter Module metadata through original aggregate-only or standalone evidence; no invented new compiler execution.','This is isolated candidate engineering only; no live installation, aggregate26 audit, production selection or complete book coverage is claimed.']}
assert not(R/OUT).exists();(R/OUT).write_text(json.dumps(body,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'offer':ref(OUT),'candidate':ref(C),'required_artifacts':len(required),'own_new_sources':2,'own_new_public_exports':48,'cross_owner_sources':1,'cross_owner_public_exports':8}))
