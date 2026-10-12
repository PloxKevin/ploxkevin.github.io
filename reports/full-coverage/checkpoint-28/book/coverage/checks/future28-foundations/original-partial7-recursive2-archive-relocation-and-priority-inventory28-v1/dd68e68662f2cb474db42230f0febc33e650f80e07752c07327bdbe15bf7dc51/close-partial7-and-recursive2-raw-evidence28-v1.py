from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def encode(j):return (json.dumps(j,indent=2)+'\n').encode()
def archive(paths,relative,scope):
    base=ROOT/relative;assert not base.exists();aliases={}
    for p in dict.fromkeys(map(Path,paths)):
        b=p.read_bytes();h=sha(p);target=base/h/p.name
        target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb')as f:f.write(b)
        assert sha(target)==h and target.read_bytes()==b
        aliases[str(p)]={'file':str(target.relative_to(ROOT)),'sha256':h}
    catalog=base/'original-closed-byte-aliases-v1.json'
    body={'status':'closed_exact_original_byte_aliases','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_file_count':len(aliases),'original_closed_byte_aliases':aliases,'scope':scope}
    with catalog.open('xb')as f:f.write(encode(body))
    return ref(catalog),aliases

partialp=Path('/tmp/foundations-literal-partial7-full-review28-v3/foundations-literal-partial7-full-review28-v3.json')
assert sha(partialp)=='8429c73be890d12639d782720ab9bb280a5bd9a4449aea37ab7ffa5d67184b2c'
partial=json.loads(partialp.read_bytes());files=[partialp]
for original,a in partial['original_closed_byte_aliases'].items():
    assert sha(original)==a['sha256']==sha(a['file'])
    assert Path(original).read_bytes()==Path(a['file']).read_bytes();files.append(Path(original))
files.extend(map(Path,['/tmp/run-foundations-literal-partial7-packaging28-v3.py','/tmp/foundations-literal-partial7-packaging-actual-v3.json','/tmp/foundations-literal-partial7-packaging-actual-v3.log']))
pc,pa=archive(files,'book/coverage/checks/future28-foundations/original-literal-partial7-full-unit-request28-v1','Original exact literal186 author request, all7 complete source bodies and dependencies; original true Lean1 failure, narrow Lean2 pass and strengthened Lean3 pass zero warnings; both author packaging schema failures and true packaging3 pass preserved. Whole literal/source approval remains pending independent full semantic review; no canonical proof/source/owner/mapping change.')

peerp=Path('/tmp/mpc-recursive16-new2-independent-foundations28-v1.json')
assert sha(peerp)=='308d97414db2edbdc1beade7fc7269e82e2b0779212d1dbeadaef7ae8225c7e4'
peer=json.loads(peerp.read_bytes());findingsp=Path(peer['original_findings']['file']);findings=json.loads(findingsp.read_bytes())
assert peer['entire_original_findings_body_and_time']==findings
for k,v in findings.items():assert peer[k]==v or k=='closed_evidence_sha256',k
for n,h in peer['closed_evidence_sha256'].items():assert sha(n)==h,n
for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner'):
    r=peer[k];assert sha(r['file'])==r['sha256']
actual=json.loads(Path(peer['actual_reader_execution']['file']).read_bytes())
assert type(actual['actual_exit_code'])is int and actual['actual_exit_code']==0
assert actual['actual_command']==['python3',peer['actual_checker']['file']] and actual['actual_workdir']==str(ROOT)
assert actual['checker_sha256_before']==actual['checker_sha256_after']==peer['actual_checker']['sha256']
assert actual['actual_runner']==peer['actual_reader_runner']
assert actual['raw_log']==peer['actual_reader_raw_log']['file'] and actual['raw_log_sha256']==peer['actual_reader_raw_log']['sha256']
assert json.loads(Path(actual['raw_log']).read_bytes())['findings']==peer['original_findings']
assert peer['component_count']==2 and all(d['approved_component']is True and d['missing_component_clauses']==[]for d in peer['component_decisions'])
assert peer['whole_exercise18_approved']is False and peer['whole_material_units_approved']is False
small=[Path(peer[k]['file'])for k in ('actual_checker','actual_reader_execution','actual_reader_raw_log','actual_reader_runner')]
mc,ma=archive(small,'book/coverage/checks/future28-foundations/original-recursive16-new2-native-reader28-v1','Exact original native reader/checker/runner/log. True0/6.713558s preserves the component-only manual semantic decisions, original failed1/pass2 bodies/times and13 inherited warnings; whole18/current55 adopted-domain and continuing composition remain pending.')
rawbase=ROOT/'book/coverage/checks/future28-foundations/original-recursive16-new2-large-review-raw-bytes28-v1';assert not rawbase.exists()
sharded={}
for p in (peerp,findingsp):
    digest=hashlib.sha256();size=0;parts=[]
    with p.open('rb')as original:
        index=0
        while True:
            b=original.read(32*1024*1024)
            if not b:break
            target=rawbase/sha(p)/(str(index).zfill(3)+'.raw-byte-part')
            target.parent.mkdir(parents=True,exist_ok=True)
            with target.open('xb')as f:f.write(b)
            assert target.read_bytes()==b
            h=hashlib.sha256(b).hexdigest();parts.append({'file':str(target.relative_to(ROOT)),'sha256':h,'bytes':len(b),'offset':size})
            digest.update(b);size+=len(b);index+=1
    assert digest.hexdigest()==sha(p) and size==p.stat().st_size
    reconstructed=hashlib.sha256();offset=0
    for part in parts:
        b=(ROOT/part['file']).read_bytes();assert sha(ROOT/part['file'])==part['sha256'] and len(b)==part['bytes'] and offset==part['offset']
        reconstructed.update(b);offset+=len(b)
    assert reconstructed.hexdigest()==sha(p) and offset==size
    sharded[str(p)]={'original_sha256':sha(p),'original_bytes':size,'concatenate_parts_in_list_order_without_changes':parts,'exact_reconstruction_sha256':reconstructed.hexdigest()}
rawcatalog=rawbase/'exact-original-raw-byte-shards-v1.json'
rawbody={'status':'closed_exact_original_large_raw_bytes_by_ordered_shards','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_files':sharded,'scope':'These ordered raw byte pieces reconstruct the exact original review and findings bytes, with every body and timestamp unchanged. The large nested originals remain TMP unchanged; this representation avoids individual files exceeding GitHub size limits. No new review, execution, retiming or whole-unit approval is claimed.'}
with rawcatalog.open('xb')as f:f.write(encode(rawbody))
retain=['status','errors','reviewer','reviewed_at_utc','completed_at_utc','component_count','source','entire_source','all16_complete_bodies_and_definitions_manually_read','entire_new2_reviewed_bodies','component_decisions','reused_primary_dependency','adopted_partial_domain_reading_qualified_current55_unchanged','whole_exercise18_approved','whole_material_units_approved','remaining_whole_source_obligations','actual_successful_trial','actual_emitted_warning_count','current_selected1175_sources31_assets5_owners_rehashed_before_after','closed_evidence_sha256','scope']
compact={k:copy.deepcopy(peer[k])for k in retain}
for k in ('actual_checker','actual_reader_execution','actual_reader_raw_log','actual_reader_runner'):compact[k]=ma[peer[k]['file']]
compact['original_large_review_exact_raw_byte_storage']={'original_review':ref(peerp),'original_findings':ref(findingsp),'ordered_original_raw_byte_shards':{'file':str(rawcatalog.relative_to(ROOT)),'sha256':sha(rawcatalog)},'entire_original_review_and_findings_body_and_times_reconstruct_exactly':True}
compact['canonical_byte_binding']={'bound_at_utc':datetime.now(timezone.utc).isoformat(),'status':'original_component_decisions_and_times_unchanged_original_full_bodies_preserved_as_exact_ordered_raw_bytes','new_mathematical_review_or_execution_claimed':False,'original_small_reader_archive_catalog':mc}
cp=ROOT/'book/coverage/checks/future28-foundations/mpc-recursive16-new2-independent-foundations28-byte-binding-v1.json'
assert not cp.exists()
with cp.open('xb')as f:f.write(encode(compact))
assert all(compact[k]==peer[k]for k in retain)

executionfiles=['/tmp/close-delivery5-and-gradient15-originals28-v1.py','/tmp/run-close-delivery5-gradient15-originals28-v1.py','/tmp/delivery5-gradient15-original-evidence-closure28-actual-v1.json','/tmp/delivery5-gradient15-original-evidence-closure28-actual-v1.log','/tmp/close-mpc8-and-allocation8-original-evidence28-v1.py','/tmp/mpc8-allocation8-original-evidence-closure28-actual-v1.json','/tmp/mpc8-allocation8-original-evidence-closure28-actual-v1.log']
ec,ea=archive(executionfiles,'book/coverage/checks/future27-core/original-delivery5-gradient15-mpc8-allocation8-closures28-v1','Exact original durable-copy helper and real execution/log bodies/times for delivery5/gradient15 and earlier MPC8/allocation8 archives. These record archive/hash closure actions only, without new mathematical proofs or production publication claims.')
print(json.dumps({'partial7_full_unit_original_catalog':pc,'recursive16_new2_native_original_catalog':mc,'recursive16_new2_large_original_shard_catalog':ref(rawcatalog),'recursive16_new2_compact_byte_binding':ref(cp),'preceding_closure_execution_catalog':ec,'original_full_review_bytes':peerp.stat().st_size,'original_findings_bytes':findingsp.stat().st_size,'largest_raw_piece_bytes':32*1024*1024,'all_rehashed_recursive_evidence_refs':len(peer['closed_evidence_sha256'])}))
