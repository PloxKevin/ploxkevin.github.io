"""Prepare exact immutable NN23 proof/review inputs, without a live ledger write."""
from pathlib import Path
from datetime import datetime, timezone
import json, hashlib, re, sys

ROOT=Path('/home/oxrexkevin/SafetyBased')
BASE=ROOT/'book/coverage/checks/modules-future23/source48'
ART=BASE/'original-artifacts'
sys.path.insert(0,str(ROOT/'book/coverage'))
from lean_names import declarations

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def relative(p):return p.relative_to(ROOT).as_posix()
def put(p,d):
    assert not p.exists(),p
    p.write_text(json.dumps(d,indent=2,ensure_ascii=False)+'\n')

BASE.mkdir(parents=True,exist_ok=True);ART.mkdir(exist_ok=True)
aliases={}
def archive(p):
    p=Path(p);assert p.is_file() and not p.is_symlink(),p
    if str(p) in aliases:return aliases[str(p)]
    d=sha(p);suffix=p.suffix or '.bin';target=ART/(d+suffix)
    if target.exists():assert sha(target)==d
    else:target.write_bytes(p.read_bytes())
    row={'path':relative(target),'sha256':d,'original_path':str(p),'original_basename':p.name}
    aliases[str(p)]=row
    return row

snapshot=ROOT/'reports/full-coverage/checkpoint-22'
baseline=ROOT/'book/coverage/modules.json'
assert sha(baseline)==sha(snapshot/'book/coverage/modules.json')=='0ebe910d6d8d9a84338727988c5d415746c3f1f624d6958997bea89645d4b06c'
manifest=read(ROOT/'reports/full-coverage/checkpoint-22-manifest.json')
selected={n:r['sha256'] for n,r in manifest['proof_files'].items()}
for n,h in selected.items():assert sha(ROOT/n)==h,n
protected={n:sha(ROOT/n) for n in ['book/coverage/modules.json','book/coverage/core.json','book/coverage/applied.json','book/coverage/foundations.json','book/coverage/inventory.json']}
protected.update({n:h for n,h in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')})
preserved=BASE/'baseline22-modules-original-v1.json'
assert not preserved.exists();preserved.write_bytes(baseline.read_bytes());assert sha(preserved)==sha(baseline)

specs=[
 ('CompleteModulesNNActivationPractices22','/tmp/nn-three-activation-practices-independent-applied-source-review23-v1.json',
  'modules-nn-activation22-canonical',14,3,['modules-nn-activation22-trial']),
 ('CompleteModulesNNInvariantPractices22','/tmp/nn-two-invariant-practices-independent-applied-source-review23-v1.json',
  'modules-nn-invariant22-canonical',14,2,['modules-nn-invariant22-trial']),
 ('CompleteModulesNNStabilityLMI23','/tmp/nn-hard2-independent-foundations-whole-source-review23-v1.json',
  'modules-nn-stabilitylmi23-canonical',11,1,['modules-nn-stabilitylmi23-trial']),
 ('CompleteModulesNNCertificateAudit23','/tmp/nn-hard4-independent-foundations-whole-source-review23-v1.json',
  'modules-nn-certificateaudit23-canonical',9,1,['modules-nn-certificateaudit23-trial']),
]
proofs=[]
for module,peerpath,stem,count,excount,histories in specs:
    source=ROOT/'verification/lean/SafeLearning'/(module+'.lean');text=source.read_text()
    names=[d['name'] for d in declarations(text) if d['kind'] in ('theorem','lemma')]
    assert len(names)==count,(module,names)
    peer=read(Path(peerpath));assert len(peer['records'])==excount
    assert all(r['whole_exercise_approved'] and not r['missing_clauses'] for r in peer['records'])
    review=archive(peerpath);review['original_review_time']=peer['reviewed_at_utc'];review['reviewer']=peer['reviewer']
    paired=[]
    for mode in ['standalone','named']:
        p=Path('/tmp')/(stem+'-'+mode+'-actual1.json');actual=read(p)
        assert actual['actual_exit_code']==0
        assert actual['source_sha256_before']==actual['source_sha256_after']==sha(source)
        assert actual['source']==relative(source)
        log=Path(actual['log']);snap=Path(actual['source_snapshot'])
        assert sha(log)==actual['log_sha256'];assert sha(snap)==actual['source_snapshot_sha256']==sha(source)
        paired.append({'actual_record':archive(p),'raw_log':archive(log),'source_snapshot':archive(snap),'actual_exit_code':0})
    history=[]
    for prefix in histories:
        for p in sorted(Path('/tmp').glob(prefix+'*.json')):
            actual=read(p);entry={'actual_record':archive(p),'actual_exit_code':actual.get('actual_exit_code')}
            for key,sha_key in [('log','log_sha256'),('source_snapshot','source_snapshot_sha256')]:
                if key in actual:
                    q=Path(actual[key]);assert sha(q)==actual[sha_key];entry[key]=archive(q)
            history.append(entry)
    proofs.append({'source':relative(source),'sha256':sha(source),'public_declarations':names,
                   'original_review':review,'actual_paired_records':paired,'original_trial_history':history})

supplement=archive('/tmp/nn-activation-node1012-explicit-declaration-scope-supplement23-v1.json')
assert supplement['sha256']=='db80ca287866da8d58e0f8efde09c1ec15156ece108c9490b457e77bdf18bdca'
for p in ['/tmp/nn-hard2-hard4-independent-foundations-execution23-v1.json']:
    execution=read(Path(p));archive(p)
    for v in execution.values():
        if isinstance(v,str) and v.startswith('/tmp/') and Path(v).is_file():archive(v)
for p in ['/tmp/modules-nn-hard23-canonical-source-preservation-v1.json',
          '/tmp/modules-future23-paired-actual-v1.py',
          '/tmp/modules-nn-hard-2-whole-source-review-request23-v1.json',
          '/tmp/modules-nn-hard-4-whole-source-review-request23-v1.json',
          '/tmp/modules-nn-activation-three-practices22-canonical-readiness-v1.json',
          '/tmp/modules-nn-invariant-two-practices22-canonical-readiness-v1.json']:
    archive(p)
for source in ['/tmp/CompleteModulesNNStabilityLMI23.lean','/tmp/CompleteModulesNNCertificateAudit23.lean']:
    archive(source)

all_ex=[];all_unit=[]
for p in proofs:
    rv=read(ROOT/p['original_review']['path'])
    all_ex.extend(r['exercise_key'] for r in rv['records'])
    all_unit.extend(r['source_unit_key'] for r in rv['material_units'])
assert len(all_ex)==len(set(all_ex))==7
assert len(all_unit)==len(set(all_unit))==43
for n,h in protected.items():assert sha(ROOT/n)==h,n
for n,h in selected.items():assert sha(ROOT/n)==h,n
alias_path=BASE/'nn-seven-practices-original-path-aliases-v1.json'
put(alias_path,{'status':'all_explicit_original_tmp_artifacts_preserved_byte_identically',
               'aliases':aliases,'scope':'Original actual JSON bodies/times/commands remain unchanged. Historical mutable input source paths in failed records are represented by their actual recorded source snapshots, never treated as current passing sources.'})
out=BASE/'nn-seven-practices-input-bindings-v1.json'
put(out,{'status':'seven_current48_whole_nn_practices_fixed_sources_and_actual_pair_inputs_ready',
 'created_at_utc':datetime.now(timezone.utc).isoformat(),
 'inventory':'book/coverage/inventory-after-correction48.json','inventory_sha256':sha(ROOT/'book/coverage/inventory-after-correction48.json'),
 'baseline22_module_ledger':{'file':relative(preserved),'sha256':sha(preserved)},
 'baseline22_live_module_ledger':{'file':'book/coverage/modules.json','sha256':sha(baseline)},
 'protected_owner_and_html_sha256':protected,
 'proof_files':proofs,
 'explicit_node1012_scope_supplement':supplement,
 'canonical_path_aliases':{'file':relative(alias_path),'sha256':sha(alias_path)},
 'whole_exercise_keys':all_ex,'material_unit_keys':all_unit,
 'counts':{'whole_exercises':7,'material_units':43,'new_sources':4,'public_theorem_lemma_exports':48,'genuine_actual_paired_records':8,'selected22_proofs_preserved':len(selected)},
 'scope':'Inputs for a NEW isolated candidate only. No live ledger/helper/offer, HTML, selection or current22 original review/evidence was changed.'})
print(json.dumps({'input_bindings':relative(out),'sha256':sha(out),'proof_files':len(proofs),'exports':48,'units':43,'whole_exercises':7,'artifact_alias_count':len(aliases)}))
