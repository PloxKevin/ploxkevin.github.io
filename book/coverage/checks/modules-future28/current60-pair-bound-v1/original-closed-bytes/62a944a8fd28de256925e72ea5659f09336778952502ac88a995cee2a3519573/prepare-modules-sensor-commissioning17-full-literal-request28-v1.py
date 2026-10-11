from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path('/home/oxrexkevin/SafetyBased')
OUT=Path('/tmp/modules-sensor-commissioning17-full-literal-request28-v1.json')
SOURCE=Path('/tmp/CompleteModulesSensorCommissioning28-draft-v4.lean')
assert not OUT.exists()
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):
 p=Path(p);return {'file':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
assert sha(ROOT/'book/coverage/inventory.json')=='6290f87b8be03fd9818dcdee4663c4f37fd159118c16e1dbeefea82a2958747a'
assert sha(SOURCE)=='bb74fce90694edb80f78e00d12582c7580314802a622d704271f6b876e7a7544'
I=json.loads((ROOT/'book/coverage/inventory.json').read_bytes()); O=json.loads((ROOT/'book/coverage/modules.json').read_bytes())
text=SOURCE.read_text(); public=re.findall(r'^theorem ([A-Za-z0-9_]+)',text,re.M); private=re.findall(r'^private theorem ([A-Za-z0-9_]+)',text,re.M)
assert len(public)==17 and len(private)==1
hist=[]
for i in range(1,5):
 p=Path('/tmp/modules-sensor-commissioning28-trial'+str(i)+'.json'); d=json.loads(p.read_bytes())
 assert type(d['actual_exit_code']) is int and d['actual_exit_code']==(1 if i<3 else 0)
 assert d['source_unchanged'] is True and d['protection_errors']==[]
 assert sha(d['source'])==d['source_sha256_before']==d['source_sha256_after']
 assert sha(d['source_snapshot'])==d['source_snapshot_sha256']==d['source_sha256_before']
 assert sha(d['raw_log'])==d['raw_log_sha256']
 hist.append({'actual_record':ref(p),'source':ref(d['source']),'source_snapshot':ref(d['source_snapshot']),'raw_log':ref(d['raw_log']),'actual_exit_code':d['actual_exit_code'],'started_at_utc':d['started_at_utc'],'finished_at_utc':d['finished_at_utc'],'elapsed_seconds':d['elapsed_seconds'],'protection_errors':d['protection_errors']})
assert hist[-1]['raw_log']['bytes']==0
old=Path('/tmp/CompleteModulesSensorCommissioning28-draft-v3.lean').read_text()
assert text.startswith(old.rsplit('end SafeLearning.CompleteModulesSensorCommissioning28',1)[0])
units=[]
for key in ['lipsdp.html::node-972','lipsdp.html::node-974']:
 u=next(u for u in I['material_source_units'] if u['key']==key)
 rows=[r for r in O['material_claims'] if key in r.get('source_unit_keys',[])]
 assert rows
 units.append({'inventory_key':key,'entire_current60_inventory_record':u,'entire_original_owner27_claim_rows':rows})
context=[u for u in I['material_source_units'] if u['source']=='SafeLearning/lipsdp.html' and 775<=u['line']<=795]
sourcehtml=(ROOT/'SafeLearning/lipsdp.html').read_text().splitlines(keepends=True)
APIS=['Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean','Mathlib/LinearAlgebra/Matrix/PosDef.lean','Mathlib/Analysis/InnerProductSpace/PiL2.lean','Mathlib/Topology/MetricSpace/Lipschitz.lean']
api=[]
for a in APIS:api.append(ref(ROOT/'verification/lean/.lake/packages/mathlib'/a))
out={'status':'prepared_full_current60_commissioning17_two_material_literals_for_independent_semantic_review','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'author':'/root/modules_finish28','source':ref(SOURCE),'public_theorem_names':['SafeLearning.CompleteModulesSensorCommissioning28.'+n for n in public],'public_theorem_count':17,'private_helper_names':private,'private_helper_count':1,'actual_current60_tmp_trial':ref('/tmp/modules-sensor-commissioning28-trial4.json'),'actual_trial_history':hist,'all15_original_passed_bodies_preserved_exact':True,'two_new_public_bridges':['actual_deployed_normalized_network_is_lipschitz','actual_sdp_gain_rounds_to_the_printed_six_decimals'],'current60_inventory':ref(ROOT/'book/coverage/inventory.json'),'current60_full_source':ref(ROOT/'SafeLearning/lipsdp.html'),'current_owner27':ref(ROOT/'book/coverage/modules.json'),'current60_application':ref(ROOT/'reports/full-coverage/source56-60-corrections-application-v1.json'),'current60_application_native':ref(ROOT/'reports/full-coverage/source56-60-corrections-application28-execution-v1.json'),'new_current60_runner':ref('/tmp/root_tmp_lean28_source60_runner_v1.py'),'new_runner_full_code_independent_guard_review':ref('/tmp/root-tmp-source60-runner-independent-modules28-closed-v1.json'),'material_units':units,'full_context_inventory_units':context,'full_exact_source_context_lines775_to795':''.join(sourcehtml[774:795]),'primary_mathlib_api_files':api,'required_semantic_decisions':['Read every full17 public body, private ReLU QC and actual definitions; full source972/974 and deployed function/input/error-budget context.','The actual sum/difference rotation is orthogonal and R^T M R equals exactly both printed2x2 blocks, with genuine zero determinants and negative traces.','The rational eigenbasis has a proved two-sided inverse, the actual M diagonalizes to[-3/2,-2,0,0], its actual characteristic polynomial is X^2(X+3/2)(X+2), and characteristic roots are exactly the printed three distinct values with multiplicity already recorded by the polynomial.','Actual matrix negative semidefiniteness is independently established by exact quadratic sum of squares and symmetry; no solver status is assumed.','Actual two ReLU incremental sector inequalities plus the same source M quadratic identity derive normalized squaredgain4/3. The EuclideanSpace Fin2 deployed function has actual Mathlib LipschitzWith sqrt(4/3), rather than a merely assumed certificate.','The physical correction is exactly twice the normalized f; actual input radius1/25 produces bound2sqrt(4/3)/25, positive and strictly less than1/10, with positive slack1/10-bound.','All three printed six-decimal numbers1.154701,0.092376,0.007624 have strict half-unit-in-last-place rational enclosures.','Assess whole972 and whole974 individually; no whole976 sharp global constant, unrelated exercise or source is claimed.'],'limits':['TMP proof only; no canonical named build, selected new aggregate, owner update or publication claimed.','Original trial1/2 failures and trial3 pass remain immutable native records with full source snapshots/logs/times.','Current60 application is actual; owner27 literal-identity rebase is still pending until Root installs a reviewed current60 owner candidate.','Current full source59 arithmetic correction is orthogonal to these unchanged972/974 literals.']}
OUT.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n')
print(json.dumps(ref(OUT)))
