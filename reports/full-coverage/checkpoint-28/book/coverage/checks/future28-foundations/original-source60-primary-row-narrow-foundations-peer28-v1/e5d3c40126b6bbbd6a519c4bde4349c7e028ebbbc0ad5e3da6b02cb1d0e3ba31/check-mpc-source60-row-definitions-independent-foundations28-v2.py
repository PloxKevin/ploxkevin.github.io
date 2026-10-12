from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util,sys,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/mpc-source60-row-definitions-independent-foundations28-v2');OUT=Path('/tmp/mpc-source60-row-definitions-independent-foundations28-findings-v2.json')
assert len(sys.argv)==3;PACKET=Path(sys.argv[1]);EXPECTED=sys.argv[2];assert not BASE.exists()and not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p;assert p.is_file()and sha(p)==r['sha256'],str(p);return p
assert sha(PACKET)==EXPECTED;j=read(PACKET);assert j['errors']==[];BASE.mkdir()
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'})
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
assert len(sel['proof_files'])==1175 and len(assets)==31 and len(owners)==5
started=datetime.now(timezone.utc).isoformat();guard();closed={str(PACKET):EXPECTED};paths={}
for k in ('current_inventory','current_source','base_source56_proposal','base_source56_candidate','base_source56_inventory','proposed_source','proposed_full29_inventory','parser','full_primary_reference'):
 p=checked(j[k]);paths[k]=p;closed[str(p)]=sha(p)
assert paths['current_inventory']==ROOT/'book/coverage/inventory.json' and paths['current_source']==ROOT/'SafeLearning/lyapunov-mpc.html'
assert sha(paths['base_source56_candidate'])=='cfd10ffdd5c689e0254bc022d330bbd5046a7e64427e40060b7a54709caeb68b'
original=paths['current_source'].read_bytes();base=paths['base_source56_candidate'].read_bytes();candidate=paths['proposed_source'].read_bytes();reps=j['raw_replacements'];assert len(reps)==2
forward=base
for r in reps:
 a,b=r['before'].encode(),r['after'].encode();assert forward.count(a)==1;forward=forward.replace(a,b)
assert forward==candidate
backward=candidate
for r in reversed(reps):
 a,b=r['before'].encode(),r['after'].encode();assert backward.count(b)==1;backward=backward.replace(b,a)
assert backward==base
for k,data in [('full_current55_context_lines500_to516',original),('full_virtual_source56_context_lines500_to516',base),('full_proposed_source60_context_lines500_to516',candidate)]:assert j[k]==''.join(data.decode().splitlines(keepends=True)[499:516])
source56=read(paths['base_source56_proposal'])
for r in source56['raw_replacements']:assert candidate.count(r['after'].encode())==1
assert 'eq. 12' not in reps[1]['after']and 'eq12'not in reps[1]['after']
assert '1-\\epsilon_k\\gt0' in reps[1]['after']and 'only for positive factors'in reps[1]['after']and 'without assuming $\\epsilon_k\\le1$'in reps[1]['after']
primary=paths['full_primary_reference'];assert sha(primary)=='f0d8687a0368e2c4eec9ea3a6bad70ea5456793c5a275b9c0f1b4a8942746c97';ls=primary.read_text().splitlines()
assert '(12)'in ls[177]and 'kf' in ls[177]and 'X̄k' in ls[231]and 'Ūk' in ls[233]
current=read(paths['current_inventory']);results=[]
sys.path.insert(0,str(ROOT/'book'))
for idx,(html,expected_inventory)in enumerate([(base,paths['base_source56_inventory']),(candidate,paths['proposed_full29_inventory'])]):
 isolated=BASE/f'case-{idx}';(isolated/'SafeLearning').mkdir(parents=True)
 for p in sorted((ROOT/'SafeLearning').glob('*.html')):shutil.copyfile(p,isolated/'SafeLearning'/p.name)
 assert len(list((isolated/'SafeLearning').glob('*.html')))==29
 (isolated/'SafeLearning/lyapunov-mpc.html').write_bytes(html)
 spec=importlib.util.spec_from_file_location(f'source60_independent_inventory_{idx}',paths['parser']);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=isolated;module.OUT=isolated/'book/coverage'
 assert module.ROOT!=ROOT and module.OUT!=ROOT/'book/coverage'and str(module.OUT).startswith(str(BASE)+'/')
 module.inventory();fresh=read(module.OUT/'inventory.json');expected=read(expected_inventory)
 assert {k:v for k,v in fresh.items()if k!='generated_at_utc'}=={k:v for k,v in expected.items()if k!='generated_at_utc'}
 assert len(fresh['source_sha256'])==29 and fresh['counts']==current['counts']and len(fresh['exercises'])==556 and len(fresh['material_source_units'])==12774
 results.append({'fresh_isolated_ROOT':str(module.ROOT),'fresh_isolated_OUT':str(module.OUT),'inventory':ref(module.OUT/'inventory.json'),'counts':fresh['counts'],'fresh_native_inventory_matches_exact_author_candidate_except_generated_at_utc':True})
old=read(Path(results[0]['inventory']['file']));new=read(Path(results[1]['inventory']['file']));expectedkeys=['lyapunov-mpc.html::node-735','lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739'];changes={}
for family in ('exercises','material_source_units'):
 a={r['key']:r for r in old[family]};b={r['key']:r for r in new[family]};assert a.keys()==b.keys();changes[family]=sorted(k for k in a if a[k]['source_text']!=b[k]['source_text'])
 for k in a:
  c,d=dict(a[k]),dict(b[k]);c.pop('source_sha256');d.pop('source_sha256')
  if k not in expectedkeys:assert c==d,k
assert changes=={'exercises':[],'material_source_units':expectedkeys}
for n,h in new['source_sha256'].items():assert h==(sha(paths['proposed_source'])if n=='SafeLearning/lyapunov-mpc.html'else current['source_sha256'][n])
owner=read(ROOT/'book/coverage/core.json')
assert j['entire_original_current55_exercise18']==next(r for r in owner['exercises']if r['inventory_key']==j['entire_original_current55_exercise18']['inventory_key'])
for r in j['entire_original_current55_claim_rows']:assert r==next(x for x in owner['material_claims']if x['id']==r['id'])
priorpath=Path('/tmp/mpc-primary-row-definitions-source60-proposal28-v1/mpc-primary-row-definitions-source60-proposal28-v1.json');assert sha(priorpath)=='6b1ffabf684b3b8174a9a40c7797aad9393cdb56cda1eeaf170197ca926cf36d';prior=read(priorpath);closed[str(priorpath)]=sha(priorpath)
assert 'eq. 12'in prior['raw_replacements'][1]['after']
original_actual=Path('/tmp/mpc-primary-row-definitions-source60-preparation-actual28-v1.json');actual=read(original_actual);assert actual['actual_exit_code']==0;closed[str(original_actual)]=sha(original_actual)
priorpeerpath=Path('/tmp/source56-wording-probability57-independent-foundations28-v2.json');assert sha(priorpeerpath)=='ff84d8e2882d24a2512a4ad9c64af5db31942d824a49b40bead7f287da90304f';priorpeer=read(priorpeerpath);closed[str(priorpeerpath)]=sha(priorpeerpath)
failedp=Path('/tmp/mpc-source60-row-definitions-independent-foundations28-actual-v1.json');failed=read(failedp);assert failed['actual_exit_code']==1;failedlog=Path(failed['raw_log']);assert sha(failedlog)==failed['raw_log_sha256']
for r in j['prior_source60_v1_originals']:p=checked(r);closed[str(p)]=sha(p)
for n,h in j['closed_evidence_sha256'].items():assert sha(n)==h;closed[n]=h
authoractualp=Path('/tmp/mpc-primary-row-definitions-source60-preparation-actual28-v2.json');aa=read(authoractualp);assert type(aa['actual_exit_code'])is int and aa['actual_exit_code']==0 and aa['protection_errors']==[]
assert aa['actual_command']==['python3','/tmp/prepare-mpc-primary-row-definitions-source60-proposal28-v2.py']and aa['actual_workdir']==str(ROOT)
assert aa['helper_sha256_before']==aa['helper_sha256_after']
for n,h in aa['helper_sha256_before'].items():assert sha(n)==h
assert aa['protected_sha256_before']==aa['protected_sha256_after']
for n,h in held.items():assert aa['protected_sha256_before'][str(ROOT/n)]==h,n
assert sha(aa['log'])==aa['log_sha256']
for p in [authoractualp,Path(aa['log']),failedp,failedlog,Path('/tmp/check-mpc-source60-row-definitions-independent-foundations28-v1.py'),Path('/tmp/run-mpc-source60-row-definitions-independent-foundations28-v1.py')]:closed[str(p)]=sha(p)
guard()
d={'status':'passed_independent_source60_primary_row_definitions_and_fresh_isolated_full29_parser_review','errors':[],'reviewer':'/root/foundations_recovery28','started_at_utc':started,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'author_request':ref(PACKET),'original_native_author_preparation':ref(authoractualp),'retained_original_independent_reader1_failure':{'ref':ref(failedp),'raw_log':ref(failedlog),'started_at_utc':failed['started_at_utc'],'finished_at_utc':failed['finished_at_utc'],'reason':'The initial reader joined splitlines without preserving the author context final newline. It stopped before any parser; NEW reader2 compares the exact keepends 500-516 slice. No source or mathematical defect.'},'whole_current55_virtual56_proposed60_context_and_changed_literal_records_read':True,'whole_pinned_primary_hertneck_paper_read':True,'primary_actual_row_locations':{'input_erosion':'lines217-219','tightening_rows':'unnumbered lines232/234 following(9)','actual_equation12':'terminal membership at line178'},'source56_adopted_domain_full_clauses_preserved_exact':True,'exact_forward_and_inverse_to_entire_virtual_source56_source':True,'independent_fresh_parser_runs':results,'actual_changed_keys_relative_virtual56':changes,'native_current_counts_unchanged':new['counts'],'approved_narrow_source_correction':True,'mathematical_scope':'For every positive real a, linear row inequalities Hx<=a*1 are equivalent to x=a*y with Hy<=1 by y=x/a and preservation of inequality under positive division; the same proof applies to Lt. At zero or negative a the row inequalities remain the definitions and scalar-set equality is not asserted. No epsilon<=1 premise or shifted-plan conclusion is inserted.','negative_factor_counterexample_checked':'In dimension1 with H rows1,-1, X=[-1,1], epsilon2, a=-1: scalar-set(-1)X contains0 but row-set requires0<=-1 and is empty. Thus the original unqualified scalar-set identity cannot serve arbitrary epsilon.','original_author_v1_attribution_decision':{'ref':ref(priorpath),'original_prepared_at_utc':prior['prepared_at_utc'],'original_native_execution':ref(original_actual),'native_execution_failed':False,'attribution_approved':False,'reason':'V1 falsely calls the unnumbered tightening rows equation12; primary equation12 is terminal membership. Its mathematical row definitions and genuine parser0 remain preserved.'},'retained_prior_source56_wording_peer':{'ref':ref(priorpeerpath),'original_reviewed_at_utc':priorpeer['reviewed_at_utc'],'body_and_time_preserved_by_exact_original_reference':True},'current_selected_proof_source_count':1175,'current_assets_guarded':31,'current_owners_guarded':5,'current55_all_held_sha256_before_and_after':held,'closed_evidence_sha256':closed,'canonical_source_owner_proof_or_publication_write_claimed':False,'compiler_or_kernel_execution_claimed':False,'whole_material_or_exercise_approved':False,'scope':'Independent narrow primary attribution/row-definition/source-text parser review. Virtual Source56 base and Source60 candidate remain unapplied; current55 exact bytes preserved. Whole exercise18 and all full-unit material decisions remain pending their own complete proofs.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'changes':changes,'whole_approved':False,'counts':new['counts']}))
