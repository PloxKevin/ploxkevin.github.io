from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');H=R/'book/coverage/retain_baseline_inputs27_v1.py';O=Path('/tmp/checkpoint27-retainer-native-independent-modules-check-result-v2.json');assert not O.exists()
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def ref(p):return {'file':p.relative_to(R).as_posix() if p.is_relative_to(R) else str(p),'sha256':sha(p)}
P=Path('/tmp/checkpoint27-retainer-independent-modules-confirmation-v1.json');assert sha(P)=='f4c978f216fc888c7d2534615bae196fc6ae2f817f6cf992a4a53e97b9b0411c';prior=json.loads(P.read_bytes());assert prior['status']=='passed' and prior['errors']==[] and prior['fixture_count']==58 and prior['helper_sha256']==sha(H)=='159d6f53b2a2a05cbc68155d2925a14dc46e90b2d47392ab32c6b822877e2d33'
ns={};exec(compile(H.read_text(),str(H),'exec'),ns)
resultp=R/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json';executionp=R/'reports/full-coverage/owner27-reviewed-candidate-integration-execution-v1.json';assert sha(resultp)=='5b6c87b7cc5e385f1e45d78dbd2340cdfa93f44d54989ef05fcd5a1ff77aa75b' and sha(executionp)=='0ca545e9860f6f96ef80bf1b7e6328bf799c3f7862b1abe8fe8be40c0c45b927'
r=json.loads(resultp.read_bytes());base=json.loads((R/ns['BASELINE']).read_bytes());m=json.loads((R/ns['MANIFEST']).read_bytes());rows={x['destination']:x for x in r['exact_replacements']}
authorization={'integration_result':ref(resultp),'actual_integration_execution':ref(executionp),'source_application':ns['APPLICATION'],'actual_source_application_execution':ns['APPLICATION_EXECUTION'],'aliases':{n:{'original_sha256':m['working_inputs_sha256'][n],'immutable_byte_copy':{'file':rows[n]['original26_byte_copy'],'sha256':rows[n]['before_sha256']}} for n in ns['OWNER_EVIDENCE_PATHS']}}
authorization['aliases'][ns['SOURCE']]={'original_sha256':ns['SOURCE_OLD_SHA'],'immutable_byte_copy':{'file':ns['SOURCE_ARCHIVE'],'sha256':ns['SOURCE_OLD_SHA']}}
got=ns['validate_evidence_aliases'](R,ns['BASELINE'],ns['MANIFEST'],authorization);assert got==authorization['aliases'] and len(got)==5
changed_rows=[];occurrences={n:0 for n in got};normalized_union={}
for n,old in base['proof_files'].items():
 normalized,used=ns['normalized_baseline_evidence'](old,got);new=copy.deepcopy(old);new['evidence_sha256']=normalized
 if used:
  new['checkpoint27_original_baseline_evidence']={'original_baseline_selection':{'file':ns['BASELINE'],'sha256':ns['BASELINE_SHA']},'original_baseline_source':n,'original_row_canonical_json_sha256':ns['canonical_row_sha256'](old),'authorized_original_path_aliases':used};changed_rows.append(n)
  for original in used:occurrences[original]+=1;assert original not in normalized and normalized[got[original]['immutable_byte_copy']['file']]==got[original]['original_sha256']
 for k,v in old.items():
  if k!='evidence_sha256':assert new[k]==v
 for p,h in normalized.items():assert p not in normalized_union or normalized_union[p]==h;normalized_union[p]=h
assert len(base['proof_files'])==1167 and all(x>0 for x in occurrences.values())
# Test the actual native algorithm's compact whole-row retrieval, without writing
# any selected row or calling retain() on production paths.
assert len(m['frozen_inputs_sha256'])==47277 and sha(R/ns['AUDIT'])==ns['AUDIT_SHA']
for n,x in rows.items():assert sha(R/n)==x['candidate']['sha256'] and sha(R/x['candidate']['file'])==x['candidate']['sha256'] and sha(R/x['original26_byte_copy'])==x['before_sha256']
pairedp=R/'book/coverage/checks/future27-core/eight-source141-canonical-v1/eight-source141-actual-canonical-paired-readiness27-v1.json';pairs=json.loads(pairedp.read_bytes());assert len(pairs['sources'])==8 and len(pairs['actual_paired_records'])==16
for n,x in base['proof_files'].items():assert sha(R/n)==x['sha256']
for x in pairs['sources']:assert sha(R/x['canonical_source'])==x['source']['sha256']
closed=copy.deepcopy(prior['closed_evidence_sha256']);closed[str(P)]=sha(P)
for p in [H,resultp,executionp,pairedp]:closed[ref(p)['file']]=sha(p)
exe=json.loads(executionp.read_bytes());closed[exe['log']]=exe['log_sha256']
for x in rows.values():closed[x['original26_byte_copy']]=x['before_sha256'];closed[x['candidate']['file']]=x['candidate']['sha256']
for n,alias in got.items():closed[alias['immutable_byte_copy']['file']]=alias['immutable_byte_copy']['sha256']
for n,h in closed.items():p=Path(n) if Path(n).is_absolute() else R/n;assert sha(p)==h
out={'status':'passed','errors':[],'reviewed_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(H),'helper_sha256':sha(H),'entire_original_full_code_and58_fixture_review_body_and_time':prior,'original_full_code_fixture_peer':ref(P),'native_authorization':authorization,'actual_installed27_authorization_validated_without_producer_call':True,'native_old_source_count':1167,'native_all_frozen26_content_count':47277,'native_changed_baseline_row_count':len(changed_rows),'native_five_alias_occurrences':occurrences,'all_original_row_fields_body_time_and_prior_provenance_retained':True,'all1175_sources_current55_fiveinstalled27_owners_exact':True,'new_semantic_or_execution_claim':False,'closed_evidence_sha256':closed,'scope':'Fresh native authorization/source-application and exact in-memory old-row normalization after actual owner27 integration0. Full original fixture report/time preserved. No retain() production call, selection output, owner write, freeze or compiler execution.'}
with O.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(json.dumps({'status':'passed','result':ref(O),'five_alias_occurrences':occurrences,'changed_rows':len(changed_rows)}))
