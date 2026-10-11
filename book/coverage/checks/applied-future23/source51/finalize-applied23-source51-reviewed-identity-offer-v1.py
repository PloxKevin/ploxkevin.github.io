from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
R=Path('/home/oxrexkevin/SafetyBased');B=R/'book/coverage/checks/applied-future23/source51';H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def P(p):
 p=Path(p);return p if p.is_absolute() else R/p
def ref(p):
 p=P(p);return {'file':str(p.relative_to(R)) if p.is_relative_to(R) else str(p),'sha256':H(p)}
a=B/'applied-audit23-candidate-source51-additions-v1.json';assert H(a)=='b0be18b27d8c6dd50c5247a920371052fe66b52bcd7cef609bf7e2c4e3c1bc34';old=json.loads(a.read_text());out=copy.deepcopy(old)
orig=[Path('/tmp/applied23-source51-identity-independent-modules-confirmation-v1.json'),Path('/tmp/modules-owner51-identity-independent-mechanics-v1.py'),Path('/tmp/applied23-source51-identity-independent-modules-actual-v1.json'),Path('/tmp/applied23-source51-identity-independent-modules-actual-v1.log')]
assert H(orig[0])=='4f4c9ec35de4c2b15612dcdb8952212b5e7d5e0dc98f5b45bb7789abc95bbba5'
peer=json.loads(orig[0].read_text());act=json.loads(orig[2].read_text());assert 'passed' in peer['status'] and not peer['errors'] and act['actual_exit_code']==0
assert H(P(act['log']))==act['log_sha256'];assert H(P(act['actual_command'][1]))==act['actual_checker_sha256_before']==act['actual_checker_sha256_after']
alias={};dest=B/'original-peer-bytes';dest.mkdir(exist_ok=True)
for p in orig:
 q=dest/p.name;assert not q.exists();q.write_bytes(p.read_bytes());assert H(q)==H(p);alias[str(p)]=ref(q);out['required_evidence_artifacts_sha256'][str(q.relative_to(R))]=H(q)
prep=B/'applied23-source51-identity-preparation-actual-execution-v1.json';pr=json.loads(prep.read_text());assert pr['actual_exit_code']==0 and H(P(pr['log']))==pr['log_sha256']
for p in [a,prep,P(pr['log']),P(out['candidate_builder']),P(out['mapped_ledger']),P(out['mapped_promotions'])]:out['required_evidence_artifacts_sha256'][str(p.relative_to(R))]=H(p)
for p,h in out['required_evidence_artifacts_sha256'].items():assert H(R/p)==h,p
out['original_unreviewed_candidate_offer']=ref(a);out['independent_final_candidate_mapping_peer']=alias[str(orig[0])];out['independent_final_candidate_mapping_actual_execution']=alias[str(orig[2])];out['independent_final_candidate_mapping_raw_log']=alias[str(orig[3])];out['actual_isolated_candidate_preparation']=ref(prep);out['canonical_path_aliases']=alias;out['independent_final_mapping_added_at_utc']=datetime.now(timezone.utc).isoformat()
rev=copy.deepcopy(out);rev['required_evidence_artifacts_sha256']=old['required_evidence_artifacts_sha256']
for k in ['original_unreviewed_candidate_offer','independent_final_candidate_mapping_peer','independent_final_candidate_mapping_actual_execution','independent_final_candidate_mapping_raw_log','actual_isolated_candidate_preparation','canonical_path_aliases','independent_final_mapping_added_at_utc']:del rev[k]
assert rev==old and out['proof_files']=={} and out['new_actual_paired_records']==[] and out['new_material_keys']==[]
q=B/'applied-audit23-candidate-source51-additions-v2-reviewed.json';assert not q.exists();q.write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({'offer':ref(q),'candidate':ref(P(out['mapped_ledger'])),'new_proofs':0,'independent_peer':out['independent_final_candidate_mapping_peer'],'scope':'Exact original offer plus completed genuine independent evidence; no live owner mutation.'}))
