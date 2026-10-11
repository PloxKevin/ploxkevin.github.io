from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys,re
ROOT=Path('/home/oxrexkevin/SafetyBased');TMP=Path('/tmp');P=ROOT/'book/coverage/checks/modules-future24/tanh-offset/three-source16-export-canonical-original-peer-binding-readiness24-v1.json';OUT=TMP/'modules-tanh16-canonical-original-body-binding-independent-foundations-review-v1.json'
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest();read=lambda p:json.loads(Path(p).read_text())
def path(n):return Path(n)if Path(n).is_absolute()else ROOT/n
def ref(p):return {'file':str(p),'sha256':H(p)}
def bind(r):
 p=path(r['file']);assert p.is_file()and not p.is_symlink()and H(p)==r['sha256'];return p
assert not OUT.exists()and H(P)=='d173dbc40dcce01de6d473948fefc78b61d990cbfe21f5787e784e0c086b7651';q=read(P)
a=read(bind(q['original_nine_body_peer']));b=read(bind(q['original_seven_bridge_peer']))
assert H(bind(q['original_nine_body_peer']))=='4f5bf305fdd4477c682b772d883de41a26de37767a27102a7fe14a5ab0d62a34'and H(bind(q['original_seven_bridge_peer']))=='8f8cb2ca30810e81f1e1a71007f2995260f027e5c8ca4122f766e189ab9c01b8'
assert q['entire_original_nine_body_peer_and_time']==a==b['entire_original_nine_body_semantics_and_time_unchanged']and q['entire_original_seven_bridge_peer_and_time']==b
assert 'passed'in a['status']and'passed'in b['status']and a['errors']==b['errors']==[]and q['whole_exercise_remains_pending']is True
assert len(q['original_path_byte_aliases'])==36
for n,r in q['original_path_byte_aliases'].items():assert H(bind(r))==H(path(n))
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
sources=[];pairs=[];names=[]
for index,z in enumerate(q['canonical_proofs']):
 p=bind(z['canonical_source']);original=bind(z['original_TMP_reviewed_source']);text=p.read_text();assert not re.search(r'\b(sorry|admit|axiom)\b',text)
 ns=[d['name']for d in declarations(text)if d['kind']in['theorem','lemma']];assert ns==z['public_theorem_names'];names+=ns
 if index==0:assert text==original.read_text()==a['entire_new_source_and_all_nine_bodies']and z['unchanged_exact_source_bytes']is True and len(ns)==9
 elif index==1:
  oldtext=b['new_sources'][0]['entire_source_and_all_twelve_bodies'];assert original.read_text()==oldtext
  first='theorem actual_literal_diagonal_products_are_nonnegative_rounded_and_not_equal'
  oldblock=oldtext[oldtext.index(first):oldtext.rindex('\nend SafeLearning.CompleteModulesNNTanhOffset24')]
  newblock=text[text.index(first):text.rindex('\nend SafeLearning.CompleteModulesNNTanhOffsetConsequences24')]
  assert oldblock==newblock and len(ns)==3 and z['unchanged_three_complete_theorem_bodies_after_new_import_and_namespace']is True
  oldnames=b['new_sources'][0]['three_new_public_names'];assert q['explicit_old_to_new_three_declaration_names']==dict(zip(oldnames,ns))
  assert text.startswith('import SafeLearning.CompleteModulesNNTanhOffset24\nimport Mathlib\n')and'open CompleteModulesNNTanhOffset24 CompleteModulesTanhNumerics CompleteModulesTanhChords'in text
 else:assert index==2 and text==original.read_text()==b['new_sources'][1]['entire_source_and_all_four_bodies']and z['unchanged_exact_source_bytes']is True and len(ns)==4
 assert len(z['actual_paired_records'])==2
 for j,pair in enumerate(z['actual_paired_records']):
  rp=bind(pair['actual_record']);r=read(rp);assert r==pair['entire_original_actual_record_body_and_time']and r['actual_exit_code']==pair['actual_exit_code']==0
  assert r['source']==z['canonical_source']['file']and r['source_sha256_before']==r['source_sha256_after']==H(p)
  cmd=['lake','env','lean',r['source'].removeprefix('verification/lean/')]if j==0 else['lake','build',r['source'].removeprefix('verification/lean/').removesuffix('.lean').replace('/','.')]
  assert r['actual_command']==cmd and r['actual_workdir']==str(ROOT/'verification/lean')and r['started_at_utc']<r['finished_at_utc']
  assert H(bind(pair['raw_log']))==r['raw_log_sha256']and bind(pair['raw_log'])==path(r['raw_log'])and bind(pair['source_snapshot']).read_bytes()==p.read_bytes()
  assert H(path(r['actual_runner']))==r['actual_runner_sha256']and r['source_snapshot_sha256']==H(bind(pair['source_snapshot']))
  for n,h in r['held23_owner_and_inventory_sha256'].items():assert H(ROOT/n)==h
  for n,h in r['exact_current51_assets_sha256'].items():assert H(ROOT/n)==h
  pairs.append({'record':pair['actual_record'],'entire_original_record_body_and_time':r,'raw_log':pair['raw_log'],'snapshot':pair['source_snapshot']})
 sources.append({'canonical_source':z['canonical_source'],'original_TMP_reviewed_source':z['original_TMP_reviewed_source'],'entire_canonical_source_and_all_bodies':text,'public_names':ns,'original_semantic_body_match':'exact_whole_source'if index!=1 else'exact_three_complete_theorem_statements_and_proof_bodies_with_new_import_and_namespace'})
assert len(set(names))==len(names)==16 and len(pairs)==6
manifest=read(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');assert len(manifest['proof_files'])==1131
for n,r in manifest['proof_files'].items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==r['sha256']
assets={n:h for n,h in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
for n,h in assets.items():assert H(ROOT/n)==H(ROOT/'reports/full-coverage/checkpoint-23'/n)==h
for n in ['core','foundations','applied','modules','applied-promotions']:
 p='book/coverage/'+n+'.json';assert H(ROOT/p)==manifest['working_inputs_sha256'][p]
assert H(ROOT/'book/coverage/inventory.json')=='d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'
report={'status':'passed_independent_three_canonical_source16_export_original_semantic_body_name_and_six_actual_paired_record_binding_only','reviewer':'/root/config21_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'checker':ref(Path(__file__)),'original_readiness':ref(P),'entire_original_nine_body_semantic_review_and_time':a,'entire_original_seven_bridge_semantic_review_and_time':b,'canonical_sources':sources,'explicit_old_to_new_three_declaration_names':q['explicit_old_to_new_three_declaration_names'],'six_actual_canonical_records_original_times_and_logs':pairs,'all36_original_trial_checker_warning_failure_bytes_exact':q['original_path_byte_aliases'],'all1131_frozen23_sources_and31_current51_assets_exact':True,'all_five_current23_live_owners_and_inventory_exact':True,'whole_exercise_and_prior_pending_scope_unchanged':True,'new_public_export_count':16,'errors':[],'coverage_complete':False,'scope':'Narrow original reviewed body/name/canonical evidence binding only. Nine and four whole source bytes exact; three complete statements and proof bodies exact in a distinct imported namespace with explicit name map. Original4f5/8f8 decisions/hypotheses/reasons/time unchanged. No repeated semantic decision, compiler rerun, exercise/answer promotion, arbitrary temporal QC theorem or current23/24 mapping/aggregate/publication inferred.'}
with OUT.open('x')as f:f.write(json.dumps(report,ensure_ascii=False,indent=2)+'\n')
print(json.dumps({'report':ref(OUT),'canonical_sources':3,'exports':16,'actual_paired_records':6}))
