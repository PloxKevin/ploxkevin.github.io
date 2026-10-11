"""New future25 exact canonical source/history preparation; no compiler command."""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,re
ROOT=Path(__file__).resolve().parents[3]
BASE=ROOT/'book/coverage/checks/foundations-future25/material-batch1'
OUT=BASE/'two-source31-export-original-history-inputs-v1.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def ref(p):return {'file':p.relative_to(ROOT).as_posix(),'sha256':sha(p)}
def copy_exact(p,q):
    q.parent.mkdir(parents=True,exist_ok=True)
    if q.exists():assert p.read_bytes()==q.read_bytes(),str(q)
    else:
        with q.open('xb') as f:f.write(p.read_bytes())
    assert sha(p)==sha(q)
def write(p,d):
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open('x') as f:json.dump(d,f,indent=2);f.write('\n')
selection=ROOT/'reports/full-coverage/checkpoint-24-selection.json'
assert sha(selection)=='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
manifest=read(ROOT/'reports/full-coverage/checkpoint-24-manifest.json')
proofs={n:d['sha256'] for n,d in manifest['proof_files'].items()};assert len(proofs)==1144
assets={n:d for n,d in manifest['working_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
owners={n:manifest['working_inputs_sha256'][n] for n in ['book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
held={**owners,'book/coverage/inventory.json':'38518673e13ed16537e301b071fb04ec0ed6720269cd14f48b986f4e82c578f3'}
def guard():
    assert sha(selection)=='9dd0a0cb80c54b728c09fc12e4327efdae621f94b5710e7a97c0d13fe92d6314'
    for n,d in {**proofs,**assets,**held}.items():assert sha(ROOT/n)==d,n
    for n,d in {**proofs,**assets}.items():assert sha(ROOT/'reports/full-coverage/checkpoint-24'/n)==d,n
guard();assert not OUT.exists()
specs=[
 {'group':'grid1175','source':'/tmp/foundations-quadratic-twenty-net24-trial5.lean','source_sha256':'3f2caf3abc7f228d63581ce31aba7144c213d830dfe5f0f009878ab2329f2a24',
  'request':'/tmp/foundations-quadratic-twenty-net25-basics1175-full-source-review-request-v1.json','request_sha256':'6542640d11bf69e95b9c3bbec501e3a5c9438b1760f2c91e6941d6c8285f8ea4',
  'peer':'/tmp/foundations-quadratic-twenty-net25-basics1175-independent-modules-full-source-review-v1.json','peer_sha256':'e950835b9a582a0fdbbb2031c799b5b8ec05abd9cb45d85807355a774713e896',
  'count':17,'whole_keys':['primer-basics.html::node-1175'],
  'patterns':['foundations-quadratic-twenty-net24-*','run-foundations-quadratic-twenty-net24-*','foundations-quadratic-net24-selected-cubic-*','run-foundations-quadratic-net24-*','foundations-quadratic-twenty-net25-*','review-foundations-quadratic-twenty-net25-*','run-owner24-source52-identities-independent-modules-actual-v1.py']},
 {'group':'calculus152-154-166','source':'/tmp/foundations-scalar-calculus25-trial4.lean','source_sha256':'7d24107b1224f26221cefece2cd054070eb78f4d6f2bfae2527707d477b49382',
  'request':'/tmp/foundations-scalar-calculus25-three-literal-full-source-review-request-v1.json','request_sha256':'453c5015ce5eed7abadc02a2b4a9d6a349664039d8bc6320ad23ec7191aa8430',
  'peer':'/tmp/foundations-scalar-calculus25-three-literals-independent-modules-full-source-review-v1.json','peer_sha256':'603fb17b9e1dd2accb4231d64ba746cf77568ba21e6a95dcebdc0cb3f2cd5696',
  'count':14,'whole_keys':['primer-optimization.html::node-152','primer-optimization.html::node-154','primer-optimization.html::node-166'],
  'patterns':['foundations-scalar-calculus25-*','run-foundations-scalar-calculus25-*','review-foundations-scalar-calculus25-*','prepare-foundations-scalar-calculus25-*']}
]
groups=[]
for item in specs:
    src=Path(item['source']);req=Path(item['request']);peerp=Path(item['peer'])
    for p,k in [(src,'source_sha256'),(req,'request_sha256'),(peerp,'peer_sha256')]:assert sha(p)==item[k]
    request=read(req);peer=read(peerp)
    assert 'passed' in peer['status'] and peer['errors']==[]
    assert peer['source']=={'file':str(src),'sha256':item['source_sha256']}
    assert peer['request']=={'file':str(req),'sha256':item['request_sha256']}
    assert peer['whole_material_units_approved']==item['whole_keys']
    namespace=re.search(r'^namespace (\S+)',src.read_text(),re.M)[1]
    names=[namespace+'.'+n for n in re.findall(r'^theorem (\w+)',src.read_text(),re.M)]
    assert names==peer['public_theorem_names'] and len(names)==item['count']
    # Keep the entire independently reviewed namespace and bytes. The grid's old
    # TMP namespace suffix24 is retained; it was never selected by checkpoint24.
    canonical=ROOT/f'verification/lean/SafeLearning/{namespace.split(".")[-1]}.lean'
    assert canonical.relative_to(ROOT).as_posix() not in proofs and not canonical.exists()
    group=BASE/item['group'];archive=group/'original-tmp-v1';originals={src,req,peerp}
    def discover(v):
        if isinstance(v,dict):
            for k,x in v.items():
                if isinstance(k,str) and k.startswith('/tmp/') and '\n' not in k and len(k)<500:
                    p=Path(k)
                    if p.is_file():
                        if isinstance(x,str) and re.fullmatch('[a-f0-9]{64}',x):assert sha(p)==x,k
                        originals.add(p)
                discover(x)
        elif isinstance(v,list):
            for x in v:discover(x)
        elif isinstance(v,str) and v.startswith('/tmp/') and '\n' not in v and len(v)<500:
            p=Path(v)
            if p.is_file():originals.add(p)
    discover(request);discover(peer)
    for pattern in item['patterns']:
        for p in Path('/tmp').glob(pattern):
            if p.is_file() and p.suffix in {'.py','.json','.lean','.log'}:originals.add(p)
    aliases={}
    for p in sorted(originals):
        target=archive/p.name;copy_exact(p,target);aliases[str(p)]=ref(target)
    copy_exact(src,canonical)
    snapshot=group/(canonical.stem+'-source-exact-canonical-v1.lean');copy_exact(src,snapshot)
    row={'status':'prepared_exact_future25_canonical_source_and_closed_original_history_pending_actual_pairs',
         'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'group':item['group'],
         'canonical_source':ref(canonical),'source_snapshot':ref(snapshot),'module':'SafeLearning.'+canonical.stem,
         'namespace_preserved_exact':namespace,'public_theorem_names':names,'public_theorem_count':len(names),
         'whole_material_unit_keys':item['whole_keys'],'original_TMP_source':aliases[str(src)],
         'original_TMP_request':aliases[str(req)],'entire_original_TMP_request_body_and_time':request,
         'original_full_semantic_peer':aliases[str(peerp)],'entire_original_full_semantic_peer_body_and_time':peer,
         'all_original_TMP_byte_aliases':aliases,'actual_compiler_execution_claimed':False,
         'scope':'Exact original source, all failed/passed TMP histories, independent peer bodies and times only. New future25 canonical pairs are still required. No live ledger, HTML, inventory, checkpoint24 selection or frozen byte change.',
         'coverage_complete':False}
    gp=group/'source-and-original-history-preparation25-v1.json';write(gp,row);groups.append(ref(gp))
guard()
result={'status':'prepared_two_exact_future25_sources31_exports4_whole_units_pending_actual_canonical_pairs',
        'prepared_at_utc':datetime.now(timezone.utc).isoformat(),'source_count':2,'public_theorem_count':31,'whole_mathematical_unit_count':4,
        'groups':groups,'baseline24_selection':ref(selection),'protected_selected24_source_sha256':proofs,
        'current52_asset_sha256':assets,'current24_owner_and_inventory_sha256':held,
        'actual_preparation_helper':ref(Path(__file__)),'actual_compiler_execution_claimed':False,'coverage_complete':False}
write(OUT,result)
print(json.dumps({'status':result['status'],'inputs':ref(OUT),'original_aliases':[len(read(ROOT/g['file'])['all_original_TMP_byte_aliases']) for g in groups]}))
