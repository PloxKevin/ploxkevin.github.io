from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,copy
ROOT=Path(__file__).resolve().parents[5];BASE='book/coverage/checks/modules-future25/source52'
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
J=lambda n:json.loads((ROOT/n).read_text())
ref=lambda n:{'file':n,'sha256':H(ROOT/n)}
orig=Path('/tmp/module25-final-candidate-independent-applied-confirmation-v1.json');assert H(orig)=='b3321e9ccd00994855bcf1c00c7f6df0b35da4ac85366953d3a8a769a03f7b03';peer=json.loads(orig.read_text());assert peer['errors']==[] and 'passed' in peer['status']
folder=ROOT/BASE/'original-final-candidate-independent-peer-v1';folder.mkdir(parents=True,exist_ok=True)
refs={};aliases=[]
for original,h in {str(orig):H(orig),**peer['closed_evidence_sha256']}.items():
 s=Path(original);p=folder/s.name;assert H(s)==h and not p.exists();p.write_bytes(s.read_bytes());assert H(p)==h;n=p.relative_to(ROOT).as_posix();refs[original]={'file':n,'sha256':h};aliases.append({'original_path':original,'canonical_file':n,'sha256':h,'size_bytes':p.stat().st_size})
catalog=folder/'original-path-alias-catalog-v1.json';assert not catalog.exists();catalog.write_text(json.dumps({'status':'six_closed_original_peer_checker_findings_actual_log_runner_bytes_preserved','aliases':aliases,'scope':'Entire original independent report body/time immutable; exact canonical aliases only.'},indent=2)+'\n')
draft=BASE+'/modules-audit25-candidate-source52-additions-draft-v1.json';o=J(draft);assert peer['offer']==ref(draft) and peer['candidate']==ref(o['module_ledger'])
for n,h in o['required_evidence_artifacts_sha256'].items():assert H(ROOT/n)==h,n
assert H(ROOT/'book/coverage/modules.json')==o['baseline24_module_ledger']['sha256'] and H(ROOT/'book/coverage/inventory.json')==o['current_inventory_sha256']
out=copy.deepcopy(o);out['status']='independently_reviewed_isolated_source52_module25_candidate_ready_for_root_copy';out['independent_final_candidate_mapping_peer_pending']=False;out['independent_final_candidate_mapping_peer']=refs[str(orig)];out['independent_final_candidate_mapping_actual_execution']=refs[peer['actual_read_only_checker']['file']];actual=json.loads(Path(peer['actual_read_only_checker']['file']).read_text());out['independent_final_candidate_mapping_raw_log']=refs[actual['raw_log']];out['entire_original_final_candidate_mechanics_body_and_time']=peer;out['original_candidate_offer_before_peer']=ref(draft);out['final_candidate_mapping_original_byte_aliases']=ref(catalog.relative_to(ROOT).as_posix());out['reviewed_offer_finalized_at_utc']=datetime.now(timezone.utc).isoformat()
for r in refs.values():out['required_evidence_artifacts_sha256'][r['file']]=r['sha256']
for n in [catalog.relative_to(ROOT).as_posix(),draft,Path(__file__).relative_to(ROOT).as_posix()]:out['required_evidence_artifacts_sha256'][n]=H(ROOT/n)
out['additional_frozen_inputs']=copy.deepcopy(out['required_evidence_artifacts_sha256'])
n=BASE+'/modules-audit25-candidate-source52-additions-v1-reviewed.json';p=ROOT/n;assert not p.exists();p.write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');print(json.dumps({'offer':ref(n),'candidate':ref(o['module_ledger']),'independent_peer':refs[str(orig)],'required_closed_artifacts':len(out['required_evidence_artifacts_sha256']),'new_sources':2,'new_exports':9}))
