"""Bind ten reviewed mathematical sources to fresh actual Source65 builds."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,importlib.util,json
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'book/coverage/checks/future29-core/current65-canonical-plan10-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def checked(r):
    p=Path(r['file']) if Path(r['file']).is_absolute() else ROOT/r['file'];assert p.is_file() and not p.is_symlink() and sha(p)==r['sha256'];return p
def read(p):return json.loads(p.read_bytes())
def ref(p):return {'file':p.relative_to(ROOT).as_posix() if p.is_relative_to(ROOT) else str(p),'sha256':sha(p)}
assert not OUT.exists()
spec=importlib.util.spec_from_file_location('plan29_names',ROOT/'book/coverage/lean_names.py');names=importlib.util.module_from_spec(spec);spec.loader.exec_module(names)
fref={'file':'book/coverage/checks/future28-foundations/owner29-approved-eight-scope-plan-v2/foundations-owner29-approved-eight-math-units-six-source-scope-plan-v2.json','sha256':'1827ef3534994d6f5d9a38e49b9ab8a0d8c531e5c7b1ede2dfe4bb7d080032be'}
aref={'file':'/tmp/applied-owner29-approved-supply-plan-v1/applied-owner29-approved-source-and-promotion-plan-v2.json','sha256':'0982d3ef1ec6638bfc50dfa3e2de50284497555486eef5057635a9c04c9ea9ff'}
sref={'file':'book/coverage/checks/modules-future29/scalar-lipsdp42-and-source65-v1/modules-scalar-lipsdp42-full-scope-independent-review-request29-current64-v3.json','sha256':'bd4713b7db552fc42f6aa6d269b28536d7f2b95773c18f9b7ec35c93b26f645b'}
# The request hash is computed from the exact durably closed body and then
# independently checked against the full semantic peer, rather than assumed.
sp=ROOT/sref['file'];sref['sha256']=sha(sp)
f,a,s=read(checked(fref)),read(checked(aref)),read(checked(sref))
scalar_peer={'file':'book/coverage/checks/future29-applied/scalar-lipsdp42-full-independent-v1/scalar-lipsdp42-full-source-independent-applied29-peer-v1.json','sha256':'b690a6d229fd067aa426216c9c9711ac9750fe917736eb0a2abf17f5c531a3ef'}
scalar_peer_body=read(checked(scalar_peer));assert scalar_peer_body['errors']==[]
assert sref['sha256'] in json.dumps(scalar_peer_body) and s['proof_source']['sha256'] in json.dumps(scalar_peer_body)
rows=[]
def add(owner,source,trial,peer,destination,expected):
    p=checked(source);d=read(checked(trial));q=read(checked(peer));assert q['errors']==[]
    assert d['actual_exit_code']==d['actual_runner_exit_code']==0 and d['protection_errors']==[]
    assert d['source_sha256_before']==d['source_sha256_after']==d['source_snapshot_sha256']==sha(p)
    assert sha(Path(d['source_snapshot']))==sha(p) and sha(Path(d['raw_log']))==d['raw_log_sha256']
    public=names.declarations(p.read_text());theorems=sum(r['kind'] in ['theorem','lemma'] for r in public);assert theorems==expected
    assert not (ROOT/destination).exists()
    rows.append({'owner':owner,'canonical_source':destination,'original_tmp_source':source,'original_actual_tmp_trial':trial,'independent_source_peers':[peer],'public_declarations':public,'public_theorem_count':theorems,'original_review_time_and_TMP_command_cwd_status_retained':True,'fresh_canonical_records_pending':True})
for r in f['proof_source_scope']:
    add('foundations',r['durable_exact_source'],r['successful_original_standalone_tmp_execution'],r['independent_full_source_correspondence_peer'],r['suggested_new_canonical_destination'],r['public_theorem_count'])
for r in a['proposed_Core_sources']:
    add('core',r['source'],r['actual_original_Lean_trial'],r['full_source_correspondence_peer'],r['proposed_canonical_source'],r['theorem_lemma_count'])
for r in a['Modules_cross_owner_review_supply']:
    add('modules',r['source'],r['actual_original_Lean_trial'],r['full_source_correspondence_peer'],r['proposed_canonical_source'],r['theorem_lemma_count'])
add('modules',s['proof_source'],s['eighth_genuine_current64_trial_same42_source']['actual_native'],scalar_peer,'verification/lean/SafeLearning/CompleteModulesScalarLipSDPOptimum29.lean',42)
assert len(rows)==10 and sum(r['public_theorem_count'] for r in rows)==202
context=Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json');assert sha(context)=='10ca7b21579a0fcd69454c1a2c211156607bd59301b2ba0bfea11e3f2dc71e78'
ctx=read(context)
for n,h in {**ctx['pins_sha256'],**ctx['held_current_source_sha256']}.items():assert sha(ROOT/n)==h,n
record={'status':'exact_reviewed_new_canonical_pair_plan29_only','prepared_at_utc':datetime.now(timezone.utc).isoformat(),'helper':ref(Path(__file__)),'context':ref(context),'source_count':10,'public_theorem_count':202,'public_name_count':sum(len(r['public_declarations']) for r in rows),'sources':rows,'original_scope_plans':[fref,aref,sref],'result_directory':'book/coverage/checks/future29-core/current65-canonical-pairs10-v1','coverage_complete':False,'canonical_owner_selection_aggregate_or_publication_claimed':False}
OUT.parent.mkdir(parents=True,exist_ok=True)
with OUT.open('xb') as output:output.write((json.dumps(record,indent=2)+'\n').encode())
print(json.dumps({'plan':ref(OUT),'source_count':10,'theorem_lemma_count':202,'public_names':record['public_name_count'],'coverage_complete':False}))
