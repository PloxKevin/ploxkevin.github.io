from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,sys,copy
ROOT=Path('/home/oxrexkevin/SafetyBased')
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations
REQUEST=Path('/tmp/foundations-scalar-calculus25-three-literal-full-source-review-request-v1.json')
OUTPUT=Path('/tmp/foundations-scalar-calculus25-three-literals-independent-modules-full-source-review-v1.json')
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def path(name):return Path(name) if Path(name).is_absolute() else ROOT/name
def ref(p):return {'file':str(p),'sha256':digest(p)}
def checked(x):
 p=path(x['file']);assert digest(p)==x['sha256'],str(p);return p
def load(x):return json.loads(checked(x).read_text())
r=json.loads(REQUEST.read_text())
assert digest(REQUEST)=='453c5015ce5eed7abadc02a2b4a9d6a349664039d8bc6320ad23ec7191aa8430'
for k in ('source','actual_standalone','inventory','selected23_manifest','current24_held_foundation_ledger','preparation_helper'):checked(r[k])
source=checked(r['source']).read_text()
assert source==r['entire_passed_source_and_all14_public_bodies']
names=[d['name'] for d in declarations(source) if d['kind'] in ('theorem','lemma')]
assert names==r['public_theorem_names'] and len(names)==14
assert all(d['kind'] in ('theorem','lemma') for d in declarations(source))
assert not any(word in source.split() for word in ('sorry','admit','axiom'))
inventory=load(r['inventory']);ledger=load(r['current24_held_foundation_ledger'])
units={u['key']:u for u in inventory['material_source_units']}
owner_before={name:digest(path(name)) for name in r['current24_installed_owner_current52_inventory_sha256']}
assert owner_before==r['current24_installed_owner_current52_inventory_sha256']
asset_before={name:digest(path(name)) for name in r['current52_all31_assets_sha256']}
assert len(asset_before)==31 and asset_before==r['current52_all31_assets_sha256']
context=r['full_current_source_context'];p=checked(context['source'])
actual_context=''.join(p.read_text().splitlines(keepends=True)[context['start_line']-1:context['end_line']])
assert actual_context==context['entire_context']
assert hashlib.sha256(actual_context.encode()).hexdigest()==context['context_sha256']
original_artifacts={};exits=[];commands=[]
for h in r['all_four_actual_trial_histories']:
 actual=load(h['actual_record']);assert actual==h['entire_original_actual_record_and_time']
 assert actual['actual_exit_code']==h['actual_exit_code'];exits.append(actual['actual_exit_code']);commands.append(actual['actual_command'])
 for a in h['all_source_log_snapshot_runner_artifacts']:
  checked(a);original_artifacts[a['file']]=a['sha256']
 assert digest(path(actual['source']))==actual['source_sha256_before']==actual['source_sha256_after']
 assert digest(path(actual['source_snapshot']))==actual['source_snapshot_sha256']==actual['source_sha256_after']
 assert digest(path(actual['raw_log']))==actual['raw_log_sha256']
 assert digest(path(actual['actual_runner']))==actual['actual_runner_sha256']
assert exits==[1,1,1,0] and len({tuple(x) for x in commands})==4
actual=load(r['actual_standalone'])
assert actual==r['all_four_actual_trial_histories'][3]['entire_original_actual_record_and_time']
assert actual['actual_command']==['lake','env','lean',r['source']['file']]
assert actual['source_sha256_before']==actual['source_sha256_after']==r['source']['sha256']
log=path(actual['raw_log']).read_text();assert log.count('warning:')==2 and 'error:' not in log
assert r['no_named_or_canonical_execution'] is True
checked(r['actual_root24_integration']);assert load(r['actual_root24_integration'])['status'].startswith('four_exact_reviewed_owner24_candidate_bytes_integrated')
selection=json.loads((ROOT/'reports/full-coverage/checkpoint-23-selection.json').read_text())
assert len(selection['proof_files'])==1131
for name,row in selection['proof_files'].items():assert digest(path(name))==row['sha256'],name
reasons=[
 'The two generic HasDerivAt proofs quantify over arbitrary real f,g and constants a,b. They retain both product contributions at the actual point; the derivative premises supply precisely the usual differentiability domain of these rules.',
 'The literal square-power derivative and exponential derivative are multiplied by the actual generic product theorem. The resulting global formula is 2x exp(x)+x² exp(x); its ordinary derivative at 1 is exactly 3 exp(1).',
 'The generic composition theorem uses the outer derivative at g(x) and the inner derivative at x. The literal triple directly exports outer 2(2x+1), inner 2, their resulting 4(2x+1), and ordinary derivative 12 at 1.',
 'Function.update varies exactly coordinate i and has velocity Pi.single i 1. Composing a genuine Fréchet derivative yields the frozen-coordinate derivative. The arbitrary normed-space curve theorem applies the entire linear derivative to its genuine full velocity; no converse from partial derivatives to differentiability is asserted.',
 'The actual shifted-square and twice-exponential functions have HasDerivAt formulas 2(x−1) and 2 exp(2x) at every real x. These are the two expressions printed in the check-before-continuing instruction.',
 'The actual objective (t−2)² on Iic 1 has IsMinOn at 1, value 1, equality only at 1, and strictly larger values for t<1. The boundary derivative is actually −2 and nonzero, so this constrained boundary optimum is distinguished from an interior stationary condition.'
]
groups=[]
for g,why in zip(r['all_six_precise_proposed_groups'],reasons):
 groups.append({'id':g['id'],'review_status':'approved_complete_source_component','decls':g['lean_declarations'],'hypotheses':g['hypotheses'],'reason':why,'missing':[]})
assert set(sum([g['decls'] for g in groups],[]))==set(names)
bygroup={g['id']:g for g in groups};decisions=[]
for u in r['material_units']:
 literal=u['entire_inventory_record'];key=literal['key'];assert units[key]==literal
 assert digest(path(literal['source']))==literal['source_sha256']
 assert hashlib.sha256(literal['source_text'].encode()).hexdigest()==literal['text_sha256']
 original=[c for c in ledger['material_claims'] if key in c.get('source_unit_keys',[])]
 assert original==u['entire_original_held24_ledger_claims']
 assert any(c['status']=='pending' for c in original)
 selected=[bygroup[g['id']] for g in u['proposed_precise_groups']]
 decisions.append({'inventory_key':key,'key':key,'inventory_record':literal,'source_sha256':literal['source_sha256'],'text_sha256':literal['text_sha256'],'review_status':'approved_complete_source_clause','status':'approved_complete_source_clause','whole_material_unit_approved':True,'decls':sum([g['decls'] for g in selected],[]),'hypotheses':sum([g['hypotheses'] for g in selected],[]),'reason':' '.join(g['reason'] for g in selected),'missing':[],'groups':[g['id'] for g in selected],'entire_original_held24_ledger_claims_preserved':original})
assert {d['key'] for d in decisions}=={'primer-optimization.html::node-152','primer-optimization.html::node-154','primer-optimization.html::node-166'}
assert owner_before=={name:digest(path(name)) for name in owner_before}
assert asset_before=={name:digest(path(name)) for name in asset_before}
result={'status':'independent_full_three_literal_source_correspondence_review_passed','errors':[],'reviewer':'/root/modules_resume','reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'request':ref(REQUEST),'inventory':r['inventory'],'source':r['source'],'entire_source_and_all14_public_bodies_read':True,'entire_source_body':source,'public_theorem_names':names,'groups':groups,'material_units':decisions,'whole_material_units_approved':[d['key'] for d in decisions],'whole_exercises_approved':[],'actual_TMP_standalone_record_reference':r['actual_standalone'],'entire_original_actual_standalone_body_and_time':actual,'entire_original_four_trial_histories_and_times':r['all_four_actual_trial_histories'],'all_original_trial_artifact_sha256':original_artifacts,'genuine_trial_exit_codes':exits,'actual_passed_raw_log_text_preserved':log,'actual_warning_count':2,'full_source_context_read':context,'all1131_selected23_source_hashes_exact':True,'current24_installed_owner_current52_inventory_sha256_before_after_exact':owner_before,'current52_all31_assets_sha256_before_after_exact':asset_before,'current_pending_claim_bodies_and_times_unchanged':True,'scope_limits':['Future25 TMP-only source-correspondence review, no canonical/named build, candidate/ledger mutation, whole-exercise promotion, or fresh kernel/aggregate execution.','Generic scalar rules require actual derivative premises at the stated points. Fréchet and curve premises are explicit; existing partial derivatives alone are not promoted to full differentiability.','Node166 contains learning advice; its embedded two derivative claims and exact constrained optimizer are individually covered. No surrounding FTC, Taylor, gradient, Hessian, or later optimization theorem is inferred.'],'actual_read_only_checker':ref(Path(__file__))}
assert not OUTPUT.exists(),'Never overwrite prior review'
OUTPUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n')
print(json.dumps({'output':str(OUTPUT),'sha256':digest(OUTPUT),'whole_units':3,'precise_groups':6,'public_theorems':14,'actual_standalone_exit_code':0,'warning_count':2}))
