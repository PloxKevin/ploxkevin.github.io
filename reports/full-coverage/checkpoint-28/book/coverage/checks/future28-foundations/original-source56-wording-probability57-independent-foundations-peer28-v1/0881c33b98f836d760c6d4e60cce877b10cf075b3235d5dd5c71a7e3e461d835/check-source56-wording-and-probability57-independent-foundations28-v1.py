from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,importlib.util,sys,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased');BASE=Path('/tmp/source56-wording-probability57-independent-foundations28-v1');OUT=Path('/tmp/source56-wording-probability57-independent-foundations28-findings-v1.json')
assert not BASE.exists()and not OUT.exists();BASE.mkdir()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def checked(r):
 p=Path(r['file']);p=p if p.is_absolute()else ROOT/p
 assert p.is_file()and sha(p)==r['sha256'],str(p)
 return p
def read(p):return json.loads(Path(p).read_text())
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json');assets=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')['exact_current55_safelearning_assets_sha256'];owners={r['destination']:r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']}
held={n:r['sha256']for n,r in sel['proof_files'].items()};held.update(assets);held.update(owners);held.update({'book/coverage/inventory.json':'82c45f6aa300ed96fd1c8e96601208b60533493d4c16790936ba6cb7b12093bf','book/coverage/material-corrections.json':'21d8394c3184dc618b944b2059c7cbb532aaac5912006d767657a72885b53f94'})
def guard():
 for n,h in held.items():assert sha(ROOT/n)==h,n
assert len(sel['proof_files'])==1175 and len(assets)==31 and len(owners)==5
started=datetime.now(timezone.utc).isoformat();guard();inv=read(ROOT/'book/coverage/inventory.json');closed={};results=[]
packets=[('/tmp/root-mpc-explicit-adopted-domain-source56-proposal-v2/root-mpc-explicit-adopted-domain-source56-proposal-v2.json','eb7c2fa86943afc11f6b199fb4946bcd8d9b6f796ceb89afab0e541e92e6e837','lyapunov-mpc.html',['lyapunov-mpc.html::node-737','lyapunov-mpc.html::node-739']),('/tmp/probability-trajectory-inputs-source56-proposal27-v1/probability-trajectory-inputs-source56-proposal27-v1.json','261ac857ae9e1fb16255e9b4bfed146d30fe54b087c24c14c100cb0ffdfda727','primer-probability.html',['primer-probability.html::node-386'])]
for idx,(name,h,page,expected)in enumerate(packets):
 assert sha(name)==h;j=read(name);closed[name]=h
 for k in ('before_inventory','source','parser','proposed_source','proposed_full29_inventory'):
  p=checked(j[k]);closed[str(p)]=sha(p)
 original=checked(j['source']).read_bytes();candidate=checked(j['proposed_source']).read_bytes()
 reps=j['raw_replacements']if idx==0 else [{'before':j['before_raw_fragment'],'after':j['after_raw_fragment']}]
 forward=original
 for r in reps:
  a,b=r['before'].encode(),r['after'].encode();assert forward.count(a)==1;forward=forward.replace(a,b)
 assert forward==candidate
 backward=candidate
 for r in reversed(reps):
  a,b=r['before'].encode(),r['after'].encode();assert backward.count(b)==1;backward=backward.replace(b,a)
 assert backward==original
 isolated=BASE/f'case-{idx}';(isolated/'SafeLearning').mkdir(parents=True)
 for p in sorted((ROOT/'SafeLearning').glob('*.html')):shutil.copyfile(p,isolated/'SafeLearning'/p.name)
 assert len(list((isolated/'SafeLearning').glob('*.html')))==29
 (isolated/'SafeLearning'/page).write_bytes(candidate)
 sys.path.insert(0,str(ROOT/'book'))
 spec=importlib.util.spec_from_file_location(f'isolated_inventory_{idx}',checked(j['parser']));module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
 module.ROOT=isolated;module.OUT=isolated/'book/coverage'
 assert module.ROOT!=ROOT and module.OUT!=ROOT/'book/coverage'and str(module.OUT).startswith(str(BASE)+'/')
 module.inventory();fresh=read(module.OUT/'inventory.json');proposed=read(checked(j['proposed_full29_inventory']))
 def stable(d):return {k:v for k,v in d.items()if k!='generated_at_utc'}
 assert stable(fresh)==stable(proposed)
 changed={}
 for family in ('exercises','material_source_units'):
  old={r['key']:r for r in inv[family]};new={r['key']:r for r in fresh[family]};assert old.keys()==new.keys()
  changed[family]=sorted(k for k in old if old[k]['source_text']!=new[k]['source_text'])
  for key in old:
   a,b=dict(old[key]),dict(new[key]);a.pop('source_sha256');b.pop('source_sha256')
   if key not in expected:assert a==b,key
 assert changed=={'exercises':[],'material_source_units':expected}
 assert len(fresh['source_sha256'])==29 and fresh['counts']==inv['counts']
 for n,v in fresh['source_sha256'].items():assert v==(sha(checked(j['proposed_source']))if n=='SafeLearning/'+page else inv['source_sha256'][n])
 if idx==0:
  old=read(checked(j['original_proposal']));prior=read(checked(j['original_independent_domain_review']));assert prior['reviewed_at_utc']=='2026-10-11T10:45:39.195330+00:00'if False else prior['approved_source_clarification_as_explicit_typed_reading']is True
  assert reps[0]==old['raw_replacements'][0]
  assert old['raw_replacements'][1]['before']==reps[1]['before']
  assert 'Here we adopt the typed-domain reading' in reps[1]['after']and'The paper does not display this membership as a separate clause'in reps[1]['after']and'extension of $V_\\delta$ to the full state space would need a separate successor-domain hypothesis'in reps[1]['after']
  for k in ('original_proposal','original_independent_domain_review'):p=checked(j[k]);closed[str(p)]=sha(p)
  decision={'approved':True,'scope':'Explicitly adopted partial-domain interpretation, not a printed primary clause or inference from total ambient contraction. Exact old local hypotheses/formula preserved; only attribution explanation clarified. No continuity of kappa or shifted feasibility inserted.','prior_original_review':j['original_independent_domain_review'],'prior_original_reviewed_at_utc':prior['reviewed_at_utc'],'whole_material_or_exercise_approved':False}
 else:
  c=j['explicit_counterexample'];assert c['initial_law']=={'0':1,'1':0};assert c['first_transition_rows']['0']==c['second_transition_rows']['0']=={'0':1,'1':0};assert c['first_transition_rows']['1']!=c['second_transition_rows']['1']
  for rows in(c['first_transition_rows'],c['second_transition_rows']):
   for row in rows.values():assert sum(row.values())==1 and all(x>=0 for x in row.values())
  assert reps==[{'before':'change any of them and every probability changes.','after':'changes to those inputs can change the trajectory law and probabilities computed from it.'}]
  for r in j['selected_primary_proof_sources'].values():p=checked(r);closed[str(p)]=sha(p)
  decision={'approved':True,'planned_source_batch':57,'scope':'Narrow false-universal-sentence correction. Both kernels keep initial0 at0 forever; unreachable row1 can differ while the complete state trajectory law is the same point mass. The new modal can-change wording is correct.','full386_context_and_counterexample_read':True,'full383_385_386_unit_gap_retained':True,'whole_material_or_exercise_approved':False,'remaining_formal_correspondence':'Actual five-factor two-step cylinder, one-step state marginal and 0.4 example, plus declared finite/general measurable scope remain pending.'}
 results.append({'packet':ref(name),'fresh_full29_parser_inventory':ref(module.OUT/'inventory.json'),'literal_changes':changed,'counts':fresh['counts'],'exact_source_forward_and_inverse_passed':True,'decision':decision})
for p,h in [(ROOT/'sources/text/hertneck.txt','f0d8687a0368e2c4eec9ea3a6bad70ea5456793c5a275b9c0f1b4a8942746c97'),(Path('/tmp/hertneck-thesis20-primary-v1.txt'),'8c52a02793853fb4739b0f8d68c31b3e6ff5957c6f22a9ae85dd1a2eeb297c27')]:assert sha(p)==h;closed[str(p)]=h
# Full primary Assumption1 plus recursive feasibility context was manually read before this measured checker.
guard()
d={'status':'passed_independent_source56_explicit_wording_and_probability57_narrow_source_review','errors':[],'reviewer':'/root/foundations_recovery28','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'started_at_utc':started,'results':results,'primary_assumption_and_recursive_proof_context_read':True,'current_selected_proof_source_count':1175,'current_assets_guarded':31,'current_owners_guarded':5,'current55_all_held_sha256_before_and_after':held,'closed_evidence_sha256':closed,'canonical_source_or_owner_or_proof_write_claimed':False,'whole_material_or_exercise_approved':False,'compiler_or_kernel_execution_claimed':False,'scope':'Independent semantic wording and exact isolated full29 parser review only. Previous source55 and checkpoint27 unchanged; proposals are not applied.'}
with OUT.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
print(json.dumps({'status':d['status'],'fresh_parser_changes':[x['literal_changes']for x in results],'whole_approved':False}))
