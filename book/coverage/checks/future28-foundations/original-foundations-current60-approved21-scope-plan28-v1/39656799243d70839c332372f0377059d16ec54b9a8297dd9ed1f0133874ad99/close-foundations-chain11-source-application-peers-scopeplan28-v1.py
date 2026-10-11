from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,shutil
ROOT=Path('/home/oxrexkevin/SafetyBased')
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def read(p):return json.loads(Path(p).read_bytes())
def ref(p):return {'file':str(p.relative_to(ROOT))if p.is_relative_to(ROOT)else str(p),'sha256':sha(p)}
selected=read(ROOT/'reports/full-coverage/checkpoint-27-selection.json')['proof_files']
def guard():
 assert len(selected)==1175
 for n,r in selected.items():assert sha(ROOT/n)==r['sha256'],n
guard();groups=[];files=[]
for helper in ('helper1','helper2'):
 stem=f'/tmp/source56-60-{helper}-readonly-ready-independent-foundations28';files.extend([Path(stem+'-source-v1.py'),Path(stem+'-actual-v1.json'),Path(stem+'-actual-v1.log'),Path(f'/tmp/run-source56-60-{helper}-readonly-ready-independent-foundations28-v1.py')]);a=read(stem+'-actual-v1.json');assert a['actual_exit_code']==(1 if helper=='helper1'else0)and a['protection_errors']==[]and sha(a['raw_log'])==a['raw_log_sha256']
 stem=f'/tmp/source56-60-{helper}-full-code-independent-foundations28';files.extend([Path(stem+'-v1.json'),Path(stem+'-findings-v1.json'),Path(stem+'-actual-v1.json'),Path(stem+'-actual-v1.log'),Path(f'/tmp/check-source56-60-{helper}-full-code-independent-foundations28-v1.py'),Path(f'/tmp/run-source56-60-{helper}-full-code-independent-foundations28-v1.py')]);p=read(stem+'-v1.json');assert p['errors']==[]and p['semantic_apply_approval']is(helper=='helper2');a=read(stem+'-actual-v1.json');assert a['actual_exit_code']==0 and sha(a['raw_log'])==a['raw_log_sha256']
groups.append(('original-source56-to60-application-helper1-failure-helper2-approved-foundations28-v1',files,'Exact full-code decisions/read-only native readiness1/2. V1 native readiness failed on valid relative evidence; its code review intentionally pending0. V2 native readiness and full code approval0. Root production execution is separate and none is claimed by this closure.'))
request=Path('/tmp/foundations-chain-lie11-four-full-units28-v1/foundations-chain-lie11-four-full-units28-v1.json');assert sha(request)=='7e8016f981e350c3a6e1bbd5ab2ec764ec0adcfbbb3c38ac163c108853a439f2';j=read(request);files=[request,Path('/tmp/prepare-foundations-chain-lie11-four-full-units28-v1.py'),Path('/tmp/foundations-chain-lie11-packet-preparation28-actual-v1.json'),Path('/tmp/foundations-chain-lie11-packet-preparation28-actual-v1.log')]
for n,r in j['original_closed_byte_aliases'].items():assert sha(n)==sha(r['file'])==r['sha256'];files.append(Path(n))
peer=Path('/tmp/foundations-chain-lie11-independent-applied-full-source-review28-v1.json');assert sha(peer)=='107609037c7adf5a8f9dfd49bef612a5699ce8e45f80cd56d02ba64d2a10f694';p=read(peer);assert p['errors']==[]and all(r['whole_unit_approved']is True and r['missing_clauses']==[]for r in p['material_units']);files.extend([peer,Path('/tmp/foundations-chain-lie11-independent-applied-findings28-v3.json')])
for v,expected in [('v1',1),('v2',1),('v3',0)]:
 stem=f'/tmp/foundations-chain-lie11-independent-applied-actual28-{v}';a=read(stem+'.json');assert a['actual_exit_code']==expected;files.extend([Path(stem+'.json'),Path(stem+'.log'),Path(f'/tmp/check-foundations-chain-lie11-independent-applied28-{v}.py'),Path(f'/tmp/run-foundations-chain-lie11-independent-applied28-{v}.py')])
groups.append(('original-chain-lie11-four-full-unit-author-and-applied-peer28-v1',files,'Four whole192/195/196/199 decisions are the exact independent Applied peer decision. Original native Lean1/0 and reviewer schema/context-newline1/1 followed by reviewer3 true0 retained unchanged. Whole timing200/backprop202 and canonical pairs/current60 candidate remain pending.'))
plan=Path('/tmp/foundations-owner28-approved21-scope-plan-v2.json');assert sha(plan)=='1e58d5cce1dcd200015a67e241cab118849dc2de218e2ac3272446898df74b86';p=read(plan);assert p['scope_counts']['whole_material_units']==21 and p['scope_counts']['public_theorem_bodies_across_exact_six_sources']==99 and p['owner_candidate_prepared']is False
files=[plan]
for v,expected in [('v1',1),('v2',0)]:
 stem=f'/tmp/foundations-owner28-approved21-scope-plan-preparation-actual-{v}';a=read(stem+'.json');assert a['actual_exit_code']==expected and sha(a['raw_log'])==a['raw_log_sha256'];files.extend([Path(stem+'.json'),Path(stem+'.log'),Path(f'/tmp/prepare-foundations-owner28-approved21-scope-plan-{v}.py'),Path(f'/tmp/run-foundations-owner28-approved21-scope-plan-preparation-{v}.py')])
groups.append(('original-foundations-current60-approved21-scope-plan28-v1',files,'Bounded typed scope plan only. Original preparer1 overly strict new-declaration schema failure retained; preparer2 physically verifies selected reuse and21 unchanged current60 literals. Six Source55 TMP true-pass sources and whole peers keep original bodies/time; current60 canonical pairs/candidate/mapping are separately pending.'))
for name,files,scope in groups:
 dest=ROOT/'book/coverage/checks/future28-foundations'/name;assert not dest.exists();dest.mkdir();aliases={};files=list(dict.fromkeys(files))
 for p in files:
  h=sha(p);q=dest/h/p.name;q.parent.mkdir(exist_ok=True);shutil.copyfile(p,q);assert p.read_bytes()==q.read_bytes();aliases[str(p)]=ref(q)
 out=dest/'original-closed-byte-aliases-v1.json'
 with out.open('x')as f:json.dump({'status':'exact_original_bytes_closed_no_new_review_or_retime','archived_at_utc':datetime.now(timezone.utc).isoformat(),'original_count':len(files),'original_sha256':{n:r['sha256']for n,r in aliases.items()},'aliases':aliases,'scope':scope,'canonical_source_owner_proof_selection_changed':False},f,indent=2);f.write('\n')
 print(json.dumps({'catalog':ref(out),'original_count':len(files)}))
guard()
