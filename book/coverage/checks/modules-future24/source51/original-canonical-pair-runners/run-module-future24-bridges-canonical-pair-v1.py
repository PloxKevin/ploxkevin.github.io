from pathlib import Path
from datetime import datetime,timezone
import subprocess,json,hashlib,time,sys
R=Path('/home/oxrexkevin/SafetyBased');name=sys.argv[1];mode=sys.argv[2];assert name in ['CompleteModulesNNTanhOffsetConsequences24','CompleteModulesNNTanhSectorClass24'] and mode in ['standalone','named-build']
S=R/'verification/lean/SafeLearning'/f'{name}.lean';D=R/'book/coverage/checks/modules-future24/tanh-offset';D.mkdir(parents=True,exist_ok=True)
J=D/f'{name}-{mode}-v1.json';L=J.with_suffix('.log');C=D/f'{name}-{mode}-source-v1.lean';assert not any(p.exists() for p in [J,L,C])
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();manifest=json.loads((R/'reports/full-coverage/checkpoint-23-manifest.json').read_text());assert len(manifest['proof_files'])==1131
proofs={n:d['sha256'] for n,d in manifest['proof_files'].items()}
guards={n:H(R/n) for n in ['book/coverage/inventory.json','book/coverage/core.json','book/coverage/foundations.json','book/coverage/applied.json','book/coverage/modules.json','book/coverage/applied-promotions.json']}
assets={n:d for n,d in manifest['frozen_inputs_sha256'].items() if n.startswith('SafeLearning/')};assert len(assets)==31
for n,d in proofs.items():assert H(R/n)==d
for n,d in assets.items():assert H(R/n)==d
C.write_bytes(S.read_bytes());before=H(S);command=['lake','env','lean','SafeLearning/'+name+'.lean'] if mode=='standalone' else ['lake','build','SafeLearning.'+name]
start=datetime.now(timezone.utc).isoformat();tick=time.monotonic()
with L.open('xb') as log:p=subprocess.run(command,cwd=R/'verification/lean',stdout=log,stderr=subprocess.STDOUT)
for n,d in {**proofs,**guards,**assets}.items():assert H(R/n)==d
assert H(S)==before==H(C)
row={'kind':'lean_standalone' if mode=='standalone' else 'named_lean_module_build','status':'passed' if p.returncode==0 else 'failed','actual_exit_code':p.returncode,'actual_command':command,'actual_workdir':str(R/'verification/lean'),'module':'SafeLearning.'+name,'source':S.relative_to(R).as_posix(),'source_sha256_before':before,'source_sha256_after':H(S),'source_snapshot':C.relative_to(R).as_posix(),'source_snapshot_sha256':H(C),'raw_log':L.relative_to(R).as_posix(),'raw_log_sha256':H(L),'actual_runner':str(Path(__file__)),'actual_runner_sha256':H(Path(__file__)),'started_at_utc':start,'finished_at_utc':datetime.now(timezone.utc).isoformat(),'elapsed_seconds':time.monotonic()-tick,'all1131_selected23_proof_sources_exact':True,'held23_owner_and_inventory_sha256':guards,'exact_current51_assets_sha256':assets,'scope':'Genuine new future24 canonical execution only. Original twelve-plus-four TMP component decisions, body scopes and review times remain unchanged; this execution does not select or globally validate the source or infer a named execution from a standalone run.'}
J.write_text(json.dumps(row,indent=2)+'\n');print(json.dumps({'record':str(J.relative_to(R)),'sha256':H(J),'actual_exit_code':p.returncode,'source_sha256':before,'raw_log_sha256':H(L)}));sys.exit(p.returncode)
