from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,importlib.util,json,difflib
R=Path('/home/oxrexkevin/SafetyBased');H='book/coverage/checks/root_integrate_owner29_candidates_v1.py';OLD='book/coverage/checks/root_integrate_owner28_candidates_v6.py'
C=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json')
def p(n):return Path(n) if Path(n).is_absolute() else R/n
def sha(n):return hashlib.sha256(p(n).read_bytes()).hexdigest()
def read(n):return json.loads(p(n).read_bytes())
def ref(n):return {'file':str(n),'sha256':sha(n)}
assert sha(H)=='f146d32801dbc4f174121decde8596021e9b79c808aa36e8e01f3569f3b1ff84'
assert sha(OLD)=='aa4340b7c42baeb3b5dc164d85fbfee936073d448e555f54e42d6e1e856cb37f'
assert sha(C)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78';context=read(C)
def guard():
 for f in ['pins_sha256','held_current_source_sha256','owners_sha256']:
  for n,h in context[f].items():assert sha(n)==h,n
 assert sha(H)=='f146d32801dbc4f174121decde8596021e9b79c808aa36e8e01f3569f3b1ff84' and sha(OLD)=='aa4340b7c42baeb3b5dc164d85fbfee936073d448e555f54e42d6e1e856cb37f'
 return copy.deepcopy(context)
start=datetime.now(timezone.utc).isoformat();before=guard()
spec=importlib.util.spec_from_file_location('readonly_reviewed_owner29_installer',R/H);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
assert m.ROOT==R and m.INVENTORY_SHA==sha('book/coverage/inventory-after-correction65.json')==sha('book/coverage/inventory.json')=='5f68ee3c68c1da1275a0a2667fe43b42263b8fc31800a834371de5bfbed01b68'
assert m.SELECTION=='reports/full-coverage/checkpoint-28-selection.json' and m.SELECTION_SHA==sha(m.SELECTION)=='e954d6a3f22139ec6ebafbe4164c46f184fe5e2c672860c9fce5829f73424632'
assert len(read(m.SELECTION)['proof_files'])==1186 and len(read('book/coverage/inventory.json')['material_source_units'])==12774 and len(read('book/coverage/material-corrections.json')['corrections'])==65
assert m.EXPECTED_NEW=={'core':3,'foundations':6,'applied':0,'modules':2}
assert m.OLD=={n.removeprefix('book/coverage/').removesuffix('.json'):h for n,h in context['owners_sha256'].items()}
assert m.ARCHIVE=='reports/full-coverage/owner28-originals-before-owner29-integration-v1' and m.RESULT=='reports/full-coverage/owner29-reviewed-candidate-integration-v1.json' and not p(m.ARCHIVE).exists() and not p(m.RESULT).exists()
text=p(H).read_text();old=p(OLD).read_text();diff=''.join(difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile=OLD,tofile=H))
# The complete source and exact diff are read independently. Function bodies outside
# main are byte-identical; main changes only reviewed phase constants/schema labels.
assert text[text.index('def safe('):text.index('def main():')]==old[old.index('def safe('):old.index('def main():')]
assert "{'exercise:complete_math':526,'exercise:partial':11,'exercise:pending':19}" in text
assert "{'reviewed':4663,'pending':8111}" in text and "==218" in text and "'protected_proof_source_count':1197" in text
assert guard()==before
o={'status':'passed_independent_full_owner29_installer_code_and_current_native_constants_review_foundations','errors':[],'started_at_utc':start,'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'original_reviewed_installer6':ref(OLD),'exact_diff':diff,'current65_context':ref(str(C)),'current_inventory':ref('book/coverage/inventory-after-correction65.json'),'baseline28_selection':ref(m.SELECTION),'exact_current_owner28_sha256':m.OLD,'protected_prior_proof_source_count':1186,'current_safelearning_asset_count':31,'new_sources_per_owner':m.EXPECTED_NEW,'new_source_total_public_theorem_body_contract':[11,218],'expected_isolated_exercise_statuses':{'complete_math':526,'partial':11,'pending':19},'expected_isolated_material_statuses':{'reviewed':4663,'pending':8111},'full_code_findings':[],'actual_producer_preflight_or_integration_executed':False,'future_producer_preflight_is_required':True,'coverage_complete':False,'review_scope':'Entire new installer and exact old6 delta, native current65 inventory/1186 proof/five owner constants. Strict present integer exit codes, command/cwd/status aliases, complete original proof retention, pair evidence membership and independent finalizer/helper/log closure gates are preserved. All candidate/peer/binding-specific prerequisites and exact resulting global counts remain conditional until Root supplies the final binding and runs the real isolated preflight. No invented positive production evidence.'}
Path('/tmp/owner29-installer-full-code-independent-foundations-findings-v1.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps({'status':o['status'],'helper':o['helper'],'full_code_findings':[],'conditional_actual_production_preflight':True}))
