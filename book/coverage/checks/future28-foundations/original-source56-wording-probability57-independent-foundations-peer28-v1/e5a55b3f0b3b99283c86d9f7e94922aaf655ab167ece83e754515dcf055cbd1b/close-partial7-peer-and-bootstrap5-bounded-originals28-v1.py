from pathlib import Path
from datetime import datetime,timezone
import hashlib,json
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):
    h=hashlib.sha256()
    with Path(p).open('rb')as f:
        while b:=f.read(1024*1024):h.update(b)
    return h.hexdigest()
def ref(p):return {'file':str(p),'sha256':sha(p)}
def read(p):return json.loads(Path(p).read_bytes())
def archive(paths,name,scope):
    base=ROOT/'book/coverage/checks/future28-foundations'/name;assert not base.exists();aliases={}
    for p in dict.fromkeys(map(Path,paths)):
        assert p.stat().st_size<50*1024*1024
        b=p.read_bytes();h=sha(p);target=base/h/p.name;target.parent.mkdir(parents=True,exist_ok=True)
        with target.open('xb')as f:f.write(b)
        assert target.read_bytes()==b and sha(target)==h
        aliases[str(p)]={'file':str(target.relative_to(ROOT)),'sha256':h}
    out=base/'original-closed-byte-aliases-v1.json'
    d={'status':'closed_exact_original_byte_aliases','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_file_count':len(aliases),'original_closed_byte_aliases':aliases,'scope':scope}
    with out.open('x')as f:json.dump(d,f,indent=2);f.write('\n')
    return ref(out)
sel=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')
assert len(sel['proof_files'])==1175
held={str(ROOT/n):r['sha256']for n,r in sel['proof_files'].items()}
bindings=read(ROOT/'book/coverage/checks/root-owner27-reviewed-candidate-bindings-v1.json')
held.update({str(ROOT/n):h for n,h in bindings['exact_current55_safelearning_assets_sha256'].items()})
held.update({str(ROOT/r['destination']):r['candidate']['sha256']for r in read(ROOT/'reports/full-coverage/owner27-reviewed-candidate-integration-v1.json')['exact_replacements']})
def guard():
    for n,h in held.items():assert sha(n)==h,n
guard()
p=Path('/tmp/foundations-literal-partial7-independent-applied-full-source-review28-v1.json')
assert sha(p)=='637035cd4581e93e3c737bdb4d463765dcf45e171b4e91654340e55379f8b20f'
j=read(p);assert j['errors']==[]and j['whole_source_unit_approved']is True and j['missing_clauses']==[]
for n,h in j['closed_evidence_sha256'].items():assert sha(n)==h,n
a=read(j['actual_independent_review']['file']);assert sha(j['actual_independent_review']['file'])==j['actual_independent_review']['sha256']
assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0 and a['protection_errors']==[]
assert a['actual_command']==['python3','/tmp/check-foundations-literal-partial7-independent-applied28-v1.py']and a['actual_workdir']==str(ROOT)
assert a['helper_sha256_before']==a['helper_sha256_after']and a['protected_sha256_before']==a['protected_sha256_after']
assert len(a['protected_sha256_before'])==38
for n,h in {**a['helper_sha256_before'],**a['protected_sha256_before']}.items():assert sha(n)==h,n
assert sha(a['log'])==a['log_sha256']
obs=read('/tmp/foundations-literal-partial7-independent-applied-observations28-v1.json')
assert obs['reviewed_at_utc']==j['reviewed_at_utc']and obs['whole_source_unit_approved']is True and obs['missing_clauses']==[]
assert json.loads(Path(a['log']).read_bytes())['sha256']==sha('/tmp/foundations-literal-partial7-independent-applied-observations28-v1.json')
req=read(j['request']['file']);assert sha(j['request']['file'])==j['request']['sha256']
assert j['entire_reviewed_new_source']==req['entire_source']and j['full_source_context']==req['full_source_context_lines129_to218']
assert j['current_pending_claims_unchanged']==req['current_pending_claims_unchanged']
assert j['material_units'][0]['entire_inventory_record']==req['full_source_units'][0]
pc=archive([p,*map(Path,['/tmp/check-foundations-literal-partial7-independent-applied28-v1.py','/tmp/run-foundations-literal-partial7-independent-applied28-v1.py','/tmp/close-foundations-literal-partial7-independent-applied28-v1.py','/tmp/foundations-literal-partial7-independent-applied-observations28-v1.json',j['actual_independent_review']['file'],a['log']])],'original-literal-partial7-independent-applied-peer28-v1','Exact original independent full-literal186 semantic approval and native reader0/body/time retained. Original peer runner freshly guarded38 inventory/corrections/assets/owner inputs, not1175 proof files; this separate closure freshly checks all1175 selected sources plus31assets/five owners before/after. No original execution scope is expanded or retimed; genuine trial1fail/2narrowpass/3strengthenedpass zero warnings retained in the exact author request. Whole owner/mapping installation remains pending Root.')
p=Path('/tmp/mpc-bootstrap27-new5-independent-foundations28-v1.json')
assert sha(p)=='4feeb2692a8505e4ce0dbcffe296f0b6c3c41c0eb301372d5bf310a79bd64b39'
j=read(p);assert j['errors']==[]and j['component_count']==5 and j['whole_exercise18_approved']is False
for n,h in j['closed_evidence_sha256'].items():assert sha(n)==h,n
for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner'):assert sha(j[k]['file'])==j[k]['sha256']
original=read(j['original_findings']['file']);assert original==j['entire_original_findings_body_and_time']
a=read(j['actual_reader_execution']['file']);assert type(a['actual_exit_code'])is int and a['actual_exit_code']==0
assert a['actual_command']==['python3',j['actual_checker']['file']]and a['actual_workdir']==str(ROOT)
assert a['checker_sha256_before']==a['checker_sha256_after']==j['actual_checker']['sha256']
assert a['actual_runner']==j['actual_reader_runner']and a['raw_log_sha256']==j['actual_reader_raw_log']['sha256']
assert json.loads(Path(a['raw_log']).read_bytes())['findings']==j['original_findings']
mc=archive([p,*[Path(j[k]['file'])for k in ('actual_checker','original_findings','actual_reader_execution','actual_reader_raw_log','actual_reader_runner')]],'original-mpc-bootstrap27-new5-bounded-peer28-v1','Original bounded full27-source/new5 component review with genuine first reader0 and exact body/time/native fail/pass histories retained. All prior original307MiB request and239MiB peer histories remain explicitly offline at SHA-bound references; they are not recursively embedded or published here. Whole18/source55 domain, Euclidean feedback conversion/scaled sets/optimizer/controller/convergence/validation composition remain pending. No canonical proof/source/owner/mapping installation.')
ec=archive(['/tmp/close-partial7-and-recursive2-raw-evidence28-v1.py','/tmp/run-close-partial7-recursive2-raw-evidence28-v1.py','/tmp/partial7-recursive2-raw-evidence-closure28-actual-v1.json','/tmp/partial7-recursive2-raw-evidence-closure28-actual-v1.log','/tmp/relocate-recursive16-large-evidence-offline28-v1.py','/tmp/run-relocate-recursive16-large-evidence-offline28-v1.py','/tmp/recursive16-large-evidence-offline-relocation28-actual-v1.json','/tmp/recursive16-large-evidence-offline-relocation28-actual-v1.log','/tmp/relocate-recursive16-large-evidence-offline28-v2.py','/tmp/run-relocate-recursive16-large-evidence-offline28-v2.py','/tmp/recursive16-large-evidence-offline-relocation28-actual-v2.json','/tmp/recursive16-large-evidence-offline-relocation28-actual-v2.log','/tmp/review-foundations-pending-families28-v1.py','/tmp/foundations-pending-whole-unit-families28-v1.json'],'original-partial7-recursive2-archive-relocation-and-priority-inventory28-v1','Exact original archive/relocation helper1 failed cross-device native1 before mutation and helper2 genuine copy/hash-verify native0; original large raw evidence stays offline. Earlier closure0 and read-only priority snapshot are retained without retiming or relabelling. Priority snapshot had14 future independently approved units before literal186 peer closed; current installed source55/owners remain unchanged. No new mathematical proof or production publication claim.')
guard()
print(json.dumps({'partial7_independent_whole_peer_original_catalog':pc,'bootstrap27_five_component_peer_original_catalog':mc,'archive_relocation_priority_original_execution_catalog':ec,'all1175_sources31_assets5_owners_rehashed_before_after':True,'root_math_or_git_mutation':False}))
