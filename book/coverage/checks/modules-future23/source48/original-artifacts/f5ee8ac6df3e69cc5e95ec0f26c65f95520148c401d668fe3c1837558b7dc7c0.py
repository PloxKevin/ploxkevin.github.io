from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
request=Path('/tmp/modules-nn-activation-three-practices22-canonical-readiness-v1.json');assert sha(request)=='c2dd4a38f68a3b1d7985966c0a3b70afa86e5aeb90cad3adbf4d46be6a76af35'
r=json.loads(request.read_text());source=ROOT/r['proof_file'];assert sha(source)==r['sha256']=='e108890e57dd11518d33f9870d0382b42b14ac19490b8a412d42127674d09750'
sys.path.insert(0,str(ROOT/'book/coverage'));from lean_names import declarations
ds=declarations(source.read_text());assert ds==r['public_declarations']
theorems=[x['name'] for x in ds if x['kind'] in ['theorem','lemma']];assert len(theorems)==14
actual=[]
for row in r['actual_execution_records']:
 p=Path(row['record']);assert sha(p)==row['record_sha256'];e=json.loads(p.read_text());assert e==row['actual_record_body']
 assert type(e['actual_exit_code']) is int and e['actual_exit_code']==0 and e['source_sha256_before']==e['source_sha256_after']==r['sha256']
 assert sha(e['log'])==e['log_sha256'] and sha(e['source_snapshot'])==e['source_snapshot_sha256']==r['sha256']
 assert e['actual_workdir']==str(ROOT/'verification/lean')
 actual.append({'record':str(p),'record_sha256':sha(p),'actual_record_body':e,'raw_log_description':'Nonempty actual four linter/deprecation warnings from the new source; named dependency warnings remain in that actual log.'})
assert len(actual)==2 and {x['actual_record_body']['kind'] for x in actual}=={'lean_standalone','named_lean_module_build'}
f=Path(r['failed_trial_record']);assert sha(f)==r['failed_trial_record_sha256'];fr=json.loads(f.read_text())
assert fr['actual_exit_code']!=0 and sha(fr['source_snapshot'])==fr['source_snapshot_sha256'] and sha(fr['log'])==fr['log_sha256']
assert sha(ROOT/r['reused_selected_helper'])==r['reused_selected_helper_sha256']
inventory=ROOT/r['inventory'];assert sha(inventory)==r['inventory_sha256']=='2daa285ff1cbc2ad0db045e00e1271b6cb58ce809f5a8328120286748250c108'
inv=json.loads(inventory.read_text());ex={x['key']:x for x in inv['exercises']};units={x['key']:x for x in inv['material_source_units']}
assert sha(ROOT/'SafeLearning/nn-in-the-loop.html')=='413846b5ffc2a5fd70f74fb6f4a24e96b7983b6a745f50340c9d2d25c75d7049'
for e in r['exact_current48_exercises']:assert e==ex[e['key']]
ns='SafeLearning.CompleteModulesNNActivationPractices22.'
def names(*a):return [ns+x for x in a]
shift=theorems[:3];sector=theorems[3:9];iqc=theorems[9:]
hshift=['Actual ReLU max(s,0) shifted at bases1 and−1; individual chord slope and origin-sector domains are all real inputs. Distinctness is established at s=1/2.']
hsector=['The actual deterministic scalar family is x_next=(6/5−d/2)x with constant d∈[alpha,1],0≤alpha≤1. Stability is strict scalar Schur/asymptotic stability; at alpha=.4 the nonzero endpoint is fixed and fails attraction, without any assertion of Lyapunov-only boundary instability. The common geometric envelope covers every initial point and every family member.']
hiqc=['The actual relation is w_t=v_t/2 and a_t=b_t=v_t/2, with zero stored previous value at time0. Every finite prefix N≥0 is quantified; no summability or infinite-horizon IQC assumption is made.']
def comp(clause,decls,hyp,why):return {'clause':clause,'lean_declarations':decls,'hypotheses':hyp,'reason':why,'approval':'approved_complete_actual_mathematical_source_component','missing_clauses':[]}
gshift=[comp('Full literal shifted-map values and inequality',shift[:1],hshift,'Exact values0/0 and1/2/0 yield two different scalar maps. This directly refutes the identical-function premise for these two channels.'),comp('Actual chord and sector QCs after an arbitrary equilibrium shift',shift[1:],hshift,'The generic shift translates every true ReLU chord and derives its inherited[0,1] slope bound and zero-centered individual sector QC. Both literal maps instantiate that genuine theorem. No coupled repeated-function assertion is inferred.')]
gsector=[comp('Actual scalar recurrence and true stability criterion',sector[:2],hsector,'The actual family iterates are multiplier^n times every initial state. Genuine Tendsto of scalar powers is equivalent to the strict absolute multiplier criterion.'),comp('All-member threshold and uniform geometric closeness',sector[2:5],hsector,'The multiplier is decreasing and ranges from7/10 to6/5−alpha/2. Every family member is asymptotically stable iff alpha>2/5, and an actual common geometric envelope gives stability uniformly over the given family.'),comp('Source endpoints, open-loop failure and positive local sector',sector[5:],hsector,'Actual multipliers6/5,19/20,1 and the fixed endpoint witness give the source0/.5/.4 comparisons. The.5 family lies in[.7,.95] and all its actual initial-state trajectories tend to zero.')]
giqc=[comp('Actual filtered channels and complete finite hard-IQC identity',iqc[:4],hiqc,'The half-activation relation makes a=b. The actual square identity is summed by induction with stored initial value0, yielding exactly both source square sums and every prefix nonnegativity.'),comp('Actual negative time sample and valid positive prefix sums',iqc[4:],hiqc,'The actual source v=(2,1) produces a=(1,1/2), terms1/−1/4 and sums1/3/4. This true sample counterexample distinguishes hard-IQC summed nonnegativity from a pointwise assumption.')]
records=[]
for key,d,hyp,groups in [('nn-in-the-loop.html#practice-easy-4',shift,hshift,gshift),('nn-in-the-loop.html#practice-medium-3',sector,hsector,gsector),('nn-in-the-loop.html#practice-medium-4',iqc,hiqc,giqc)]:
 e=ex[key];records.append({'exercise_key':key,'exercise_text_sha256':e['text_sha256'],'source':e['source'],'source_sha256':e['source_sha256'],'entire_inventory_record':e,'review_status':'approved_complete_source','whole_exercise_approved':True,'independent_whole_source_review_passed':True,'hypotheses':hyp,'lean_declarations':d,'reviewed_components':groups,'missing_clauses':[],'per_exercise_reason':'The exact full question, hint and every worked step correspond to the actual mathematical declarations within the stated family, domain and finite-prefix hypotheses. Optional study navigation is classified separately.'})
specs=[
(997,shift,hshift,'The full two-map value/distinctness question is answered by the actual exact values and true individual shift theorem.'),
(998,[],[],'Only optional navigation to background and the local page section; it asserts no mathematical theorem or linked result.'),
(1004,shift,hshift,'The two literal basepoints are on opposite sides of the actual ReLU kink; the formulas and explicit values show why equal origin values do not imply identical maps.'),
(1008,shift[:1],hshift,'Both exact actual origin values are zero, with the displayed ReLU evaluations.'),
(1010,shift[:1],hshift,'The actual1/2 and0 values give the genuine function inequality.'),
(1012,shift[1:],hshift,'The full generic chord/sector shift theorem and both exact instantiations preserve individual QCs. The earlier explicit unequal-map theorem invalidates using an identical-function premise between these two channels.'),
(1058,sector,hsector,'Every actual family trajectory and all-member strict stability iff supply the complete requested threshold and0/.5 comparison.'),
(1059,[],[],'Only optional background links; no mathematical claim or linked whole theorem is approved by association.'),
(1065,sector[:2],hsector,'The exact actual scalar multiplier and its absolute-value strict criterion give the stated hint.'),
(1069,sector[2:3],hsector,'Actual decreasing multiplier and full range prove both source endpoints and positivity.'),
(1071,sector[3:5]+sector[5:],hsector,'The derived all-member iff is alpha>2/5; the true constant endpoint at2/5 fails attraction. Actual common envelope establishes the uniform strict-stability reading.'),
(1073,sector[5:],hsector,'The genuine0/.5 comparisons give the unstable open-loop Schur coefficient6/5 and stable[.7,.95] family. The lower-sector interpretation is scoped to this actual scalar uncertainty family.'),
(1078,iqc,hiqc,'Actual filtered equality, numerical source terms and finite-prefix square identity answer every clause of the question.'),
(1079,[],[],'Only optional references to sequence sums and the local discussion, with no new mathematical assertion.'),
(1085,iqc[:2],hiqc,'The actual half-map equality and true square identity match both hint clauses.'),
(1089,iqc[4:],hiqc,'Actual source values give1/−1/4 and the two partial sums1/3/4.'),
(1091,iqc[1:4],hiqc,'Actual generic every-finite-prefix telescoping with zero previous initial value yields exactly the two half-square sums and nonnegativity.'),
(1093,iqc[2:],hiqc,'The genuine every-prefix result and explicit negative sample support precisely the hard-IQC interpretation. No neighboring general Lyapunov proof is promoted.')]
materials=[]
for node,d,hyp,why in specs:
 key='nn-in-the-loop.html::node-'+str(node);u=units[key];assert hashlib.sha256(u['source_text'].encode()).hexdigest()==u['text_sha256']
 nf=node in [998,1059,1079]
 materials.append({'source_unit_key':key,'entire_inventory_record':u,'source':u['source'],'source_sha256':u['source_sha256'],'unit_text_sha256':u['text_sha256'],'source_text':u['source_text'],'line':u['line'],'locator':u['locator'],'review_status':'approved_nonformal_source_scope' if nf else 'approved_complete_source','material_status':'nonformal' if nf else 'proved','whole_unit_approved':True,'per_unit_reason':why,'hypotheses':hyp,'lean_declarations':d,'missing_clauses':[]})
assert len(materials)==18 and sum(x['material_status']=='proved' for x in materials)==15
m=json.loads((ROOT/'reports/full-coverage/checkpoint-21-manifest.json').read_text());assert len(m['proof_files'])==1089
for p,row in m['proof_files'].items():assert sha(ROOT/p)==row['sha256']
helper=r['reused_selected_helper'];assert m['proof_files'][helper]['sha256']==r['reused_selected_helper_sha256']
for p,digest in m['proof_files'][helper]['evidence_sha256'].items():assert sha(ROOT/p)==digest
out={'schema_version':1,'status':'passed_independent_whole_nn_activation_three_practices_source48_review_future23','reviewer':'/root/applied_next','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'inventory':r['inventory'],'inventory_sha256':r['inventory_sha256'],'request':str(request),'request_sha256':sha(request),'records':records,'material_units':materials,'proof_source_sha256':{r['proof_file']:r['sha256']},'actual_execution_records':actual,'all14_complete_theorem_bodies_and10_definitions_read':True,'failed_trial_record':str(f),'failed_trial_record_sha256':sha(f),'failed_trial_body':fr,'retained_selected_helper':m['proof_files'][helper],'counts':{'whole_exercises':3,'physical_units':18,'proved':15,'nonformal':3,'public_theorems':14},'protected21_selected_sources':{'count':1089,'all_sha256_exact':True},'independent_checker':str(Path(__file__)),'independent_checker_sha256':sha(__file__),'scope':['This fresh review is outside the current checkpoint22 production cutoff. No current source/ledger/offer/selection mutation or new compiler execution is claimed.','Every physical question/hint/step is read directly; explicit optional links are individually nonformal.','The stability criterion is strict Schur/asymptotic scalar stability. Fixed endpoint multiplier1 is not called Lyapunov unstable.','The finite IQC is proved for the actual half-activation with zero previous input; no general repeated-activation or arbitrary uncertainty IQC theorem is inferred.'],'errors':[]}
p=Path('/tmp/nn-three-activation-practices-independent-applied-source-review23-v1.json')
with p.open('x') as f:json.dump(out,f,indent=2,ensure_ascii=False);f.write('\n')
print(json.dumps({'review':str(p),'sha256':sha(p),'whole_exercises':3,'physical_units':18}))
