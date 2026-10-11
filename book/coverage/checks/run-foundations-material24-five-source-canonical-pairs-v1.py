"""Actual unique future24 canonical pairs; frozen23 selection and current owners stay exact."""
from pathlib import Path
from datetime import datetime,timezone
import json,hashlib,re,subprocess,time
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future24/material-batch1'
INPUT=Path('/tmp/foundations-material24-five-source-pair-inputs-v1.json')
H=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
R=lambda p:json.loads(Path(p).read_text())
def ref(p):return {'file':str(Path(p).relative_to(ROOT)),'sha256':H(p)}
def write(p,row):
 with p.open('x')as f:f.write(json.dumps(row,indent=2)+'\n')
def copy_exact(a,b):
 if b.exists():assert b.read_bytes()==a.read_bytes(),str(b)
 else:
  with b.open('xb')as f:f.write(a.read_bytes())
 assert H(a)==H(b)
inputs=R(INPUT);assert len(inputs)==5 and sum(x['theorem_count']for x in inputs)==37
selectionp=ROOT/'reports/full-coverage/checkpoint-23-selection.json'
assert H(selectionp)=='9831539a3b2be8c9d7878fd004354511aa332b203e40506233d0a000dca805fb'
manifest=R(ROOT/'reports/full-coverage/checkpoint-23-manifest.json');selection=R(selectionp)
assert manifest['selection_sha256']==H(selectionp)and len(manifest['proof_files'])==len(selection['proof_files'])==1131
proofs={n:row['sha256']for n,row in manifest['proof_files'].items()}
assets={n:d for n,d in manifest['working_inputs_sha256'].items()if n.startswith('SafeLearning/')};assert len(assets)==31
owners={n:manifest['working_inputs_sha256'][n]for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
guards={**proofs,**assets,**owners,'book/coverage/inventory.json':'d746b68d38ff05c22285b27dbfc23bcd961bdfeeaeab6b6d44355bd6db1e3d41'}
def guard():
 assert H(selectionp)=='9831539a3b2be8c9d7878fd004354511aa332b203e40506233d0a000dca805fb'
 for n,d in guards.items():assert H(ROOT/n)==d,n
 for n,d in {**proofs,**assets}.items():assert H(ROOT/'reports/full-coverage/checkpoint-23'/n)==d,n
guard();BASE.mkdir(parents=True,exist_ok=True);copy_exact(INPUT,BASE/INPUT.name)
groups=[]
for item in inputs:
 group=BASE/item['group'];group.mkdir(exist_ok=True);archive=group/'original-tmp';archive.mkdir(exist_ok=True)
 source=Path(item['source']);requestp=Path(item['request']);peerp=Path(item['peer'])
 assert H(source)==item['source_sha256']and H(requestp)==item['request_sha256']and H(peerp)==item['peer_sha256']
 request=R(requestp);peer=R(peerp);assert 'passed'in peer['status']
 namespace=re.search(r'^namespace (\S+)',source.read_text(),re.M)[1];name=namespace.split('.')[-1]
 names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',source.read_text(),re.M)];assert len(names)==item['theorem_count']
 canonical=ROOT/f'verification/lean/SafeLearning/{name}.lean';assert str(canonical.relative_to(ROOT))not in proofs and not canonical.exists()
 originals={source,requestp,peerp,INPUT,*[Path(x)for x in item['extra_originals']]}
 def discover(v):
  if isinstance(v,dict):
   for x in v.values():discover(x)
  elif isinstance(v,list):
   for x in v:discover(x)
  elif isinstance(v,str)and v.startswith('/tmp/')and'\n'not in v and len(v)<500 and Path(v).is_file():originals.add(Path(v))
 discover(request);discover(peer)
 # Close reader execution provenance explicitly even when the semantic report binds its checker only.
 stems={'orthonormal121':'modules-refresher-orthonormal121','coercivity1150':'foundations-coercivity-margin24','extreme-value1145-1147':'modules-extreme-value-two-literal-peer24','printed-route1158':'foundations-compact-lyapunov-printed-route24','audit1163':'modules-foundations-audit1163'}
 for p in Path('/tmp').glob(stems[item['group']]+'*'):
  if p.is_file()and p.suffix in {'.py','.json','.log','.lean'}:originals.add(p)
 copies={}
 for p in sorted(originals):
  target=archive/p.name;copy_exact(p,target);copies[str(p)]=ref(target)
 copy_exact(source,canonical);snapshot=group/(name+'-canonical-source-v1.lean');copy_exact(source,snapshot)
 pairs=[]
 # Named target first establishes any source-exact imported dependencies. Both commands are recorded honestly.
 for mode,cmd in [('named-build',['lake','build','SafeLearning.'+name]),('standalone',['lake','env','lean','SafeLearning/'+name+'.lean'])]:
  record=group/(name+'-'+mode+'-actual-v1.json');log=group/(name+'-'+mode+'-actual-v1.log')
  assert not record.exists()and not log.exists();guard();before=H(canonical);start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
  with log.open('xb')as f:actual=subprocess.run(cmd,cwd=ROOT/'verification/lean',stdout=f,stderr=subprocess.STDOUT)
  finish=datetime.now(timezone.utc).isoformat();elapsed=time.monotonic()-tick
  row={'kind':'actual_future24_canonical_'+mode,'status':'passed'if actual.returncode==0 else'failed',
       'source':str(canonical.relative_to(ROOT)),'source_sha256_before':before,'source_sha256_after':H(canonical),'source_unchanged':before==H(canonical),
       'source_snapshot':str(snapshot.relative_to(ROOT)),'source_snapshot_sha256':H(snapshot),
       'actual_command':cmd,'actual_workdir':str(ROOT/'verification/lean'),'actual_exit_code':actual.returncode,
       'started_at_utc':start,'finished_at_utc':finish,'elapsed_seconds':elapsed,'log':str(log.relative_to(ROOT)),'log_sha256':H(log),
       'actual_pair_helper':str(Path(__file__).relative_to(ROOT)),'actual_pair_helper_sha256':H(__file__),
       'all1131_frozen23_selected_sources_exact':True,'scope':'Genuine new unselected future24 canonical compiler command. No live owner/source/inventory amendment, selection24, aggregate24 or checkpoint23 proof leak.'}
  write(record,row);pairs.append({'actual_record':ref(record),'raw_log':ref(log),'source_snapshot':ref(snapshot),'actual_exit_code':actual.returncode})
  assert before==H(canonical)==item['source_sha256'];guard()
  print(json.dumps({'group':item['group'],'mode':mode,'actual_exit_code':actual.returncode,'elapsed_seconds':elapsed}),flush=True)
  if actual.returncode:raise SystemExit(actual.returncode)
 result={'status':'passed_actual_future24_source_exact_canonical_pair_original_whole_semantics_and_times_retained',
         'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'group':item['group'],'canonical_source':ref(canonical),'canonical_source_snapshot':ref(snapshot),
         'public_theorem_names':names,'public_theorem_count':len(names),'actual_canonical_pair':pairs,
         'original_TMP_request':copies[str(requestp)],'entire_original_TMP_request_body_and_time':request,
         'original_full_semantic_peer':copies[str(peerp)],'entire_original_full_semantic_peer_body_and_time':peer,
         'all_original_TMP_byte_copies':copies,'actual_helper':ref(Path(__file__)),
         'all1131_selected23_sources_and_frozen_snapshots_exact':True,'all31_source51_assets_and_snapshots_exact':True,'all_five_live23_owner_ledgers_and_inventory_exact':True,
         'scope':'Only actual canonical source/evidence closure added. Original whole semantic decisions/body/time unchanged. Narrow independent canonical binding and isolated candidate24 remain separate.',
         'coverage_complete':False}
 out=group/'source-exact-canonical-paired-readiness24-v1.json';write(out,result);groups.append(ref(out))
guard();final={'status':'passed_actual_five_source37_export_canonical_pairs_future24_only','prepared_at_utc':datetime.now(timezone.utc).isoformat(),
              'source_count':5,'public_theorem_count':37,'whole_mathematical_unit_count':6,'groups':groups,'actual_helper':ref(Path(__file__)),
              'all1131_selected23_sources_exact':True,'all31_source51_assets_and_snapshots_exact':True,'all_five_live23_owners_inventory_exact':True,
              'scope':'Future24 isolated canonical pairs only, with full original failed/passed TMP histories and semantic times. No current23 proof selection/owner or HTML change.',
              'coverage_complete':False}
out=BASE/'five-source37-export-actual-canonical-readiness24-v1.json';write(out,final);print(json.dumps({'readiness':ref(out),'status':final['status']}),flush=True)
