"""Pair one immutable future23 source after Root releases shared named builds."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT=Path(__file__).resolve().parents[3]
LEAN=ROOT/"verification/lean"
BASE=ROOT/"book/coverage/checks/foundations-future23/finite-prefix"
TMP=Path("/tmp/foundations-finite-prefix23-trial3.lean")
DIGEST="f10296c36c25f094374c32423ba6d837f6bd364e397a89c7a586192d1d0bf7ef"
NAME="CompleteFoundationsFinitePrefix23"
CANONICAL="verification/lean/SafeLearning/"+NAME+".lean"
BINDINGS="book/coverage/checks/root-owner22-reviewed-candidate-bindings-v3.json"
BINDINGS_SHA="8b39f77d1f8ead44b6b20d6a759434173b61c852a871a0b6805923c0d4c29b7f"
REQUEST="/tmp/foundations-finite-prefix23-source-review-request-v1.json"
REQUEST_SHA="a4b50adbef83edc70fa674beef20fb478a0bc4c810c558b2cea3d70c73361708"

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read(path):return json.loads(path.read_text())
def relative(path):return path.relative_to(ROOT).as_posix()
def new_json(path,data):
    with path.open("x") as output:output.write(json.dumps(data,ensure_ascii=False,indent=2)+"\n")
def exact_copy(original,target):
    if target.exists():assert target.read_bytes()==original.read_bytes()
    else:
        with target.open("xb") as output:output.write(original.read_bytes())
    assert sha(target)==sha(original)

assert sha(TMP)==DIGEST and sha(Path(REQUEST))==REQUEST_SHA
assert sha(ROOT/BINDINGS)==BINDINGS_SHA
bindings=read(ROOT/BINDINGS)
protected={**bindings["new_immutable_proof_sources_sha256"],**bindings["exact_current48_safelearning_assets_sha256"]}
old=read(ROOT/"reports/full-coverage/checkpoint-21-manifest.json")
protected.update({name:row["sha256"] for name,row in old["proof_files"].items()})
protected.update({row["held21_ledger"]:row["candidate_ledger"]["sha256"] for row in bindings["owners"].values()})
protected["book/coverage/inventory.json"]=bindings["inventory_sha256"]
protected["book/coverage/foundations-audit22-source48-additions-v3.json"]="c08b048a3ec9cb9fbf06fa45e68f6503c3f4daaeab561140dbe6c13fe5b17638"

def verify_protected():
    for name,digest in protected.items():assert sha(ROOT/name)==digest,name

verify_protected()
BASE.mkdir(parents=True,exist_ok=True)
archive=BASE/"original-tmp";archive.mkdir(exist_ok=True)
originals=[]
for n in [1,2,3]:
    for suffix in ["lean","json","log"]:originals.append(Path("/tmp/foundations-finite-prefix23-trial"+str(n)+"."+suffix))
originals.extend([Path(REQUEST),Path("/tmp/foundations-finite-prefix23-request-assembly-observed-failure-v1.json")])
archived={}
for original in originals:
    target=archive/original.name
    exact_copy(original,target)
    archived[str(original)]={"canonical_copy":relative(target),"sha256":sha(target)}
canonical=ROOT/CANONICAL
exact_copy(TMP,canonical)
snapshot=BASE/(NAME+"-source-v1.lean")
exact_copy(TMP,snapshot)
assert len(re.findall(r"^theorem ",canonical.read_text(),re.M))==6
pairs=[]
for suffix,command in [("standalone",["lake","env","lean","SafeLearning/"+NAME+".lean"]),("named-build",["lake","build","SafeLearning."+NAME])]:
    record=BASE/(NAME+"-"+suffix+"-v1.json")
    log=BASE/(NAME+"-"+suffix+"-v1.log")
    assert not record.exists() and not log.exists()
    assert sha(canonical)==DIGEST
    started=datetime.now(timezone.utc).isoformat();t=time.monotonic()
    with log.open("xb") as output:result=subprocess.run(command,cwd=LEAN,stdout=output,stderr=subprocess.STDOUT,check=False)
    finished=datetime.now(timezone.utc).isoformat()
    assert sha(canonical)==DIGEST
    data={"source":CANONICAL,"source_sha256_before":DIGEST,"source_sha256_after":sha(canonical),"preserved_source":relative(snapshot),"preserved_source_sha256":sha(snapshot),"command":command,"actual_workdir":str(LEAN),"actual_exit_code":result.returncode,"started_at_utc":started,"finished_at_utc":finished,"elapsed_seconds":time.monotonic()-t,"log":relative(log),"log_sha256":sha(log),"original_TMP_passing_record":archived["/tmp/foundations-finite-prefix23-trial3.json"],"scope":"Actual canonical future23 execution only. Exact already selected21 and reviewed22 proof sources, current22 candidate ledgers/offers and current48 assets remain unchanged; no aggregate23 or coverage selection claim."}
    new_json(record,data)
    pairs.append({"file":relative(record),"sha256":sha(record),"raw_log":{"file":relative(log),"sha256":sha(log)},"actual_exit_code":result.returncode})
    verify_protected()
    if result.returncode!=0:raise SystemExit(result.returncode)
request=read(Path(REQUEST))
request["original_TMP_request"]={"file":relative(archive/Path(REQUEST).name),"sha256":REQUEST_SHA}
request["status"]="canonical_future23_actual_zero_pair_complete_literal_peer_requested"
request["canonical_pair_prepared_at_utc"]=datetime.now(timezone.utc).isoformat()
request["new_proof_source"]=CANONICAL
request["new_proof_source_sha256"]=DIGEST
request["canonical_pair_pending"]=False
request["actual_canonical_pair"]=pairs
request["exact_original_TMP_byte_copies"]=archived
request["actual_pair_helper"]={"file":relative(Path(__file__)),"sha256":sha(Path(__file__))}
request["unchanged21_1089_and_reviewed22_24_source_hashes_checked"]=True
request["unchanged_current22_owner_ledgers_sha256"]={row["held21_ledger"]:row["candidate_ledger"]["sha256"] for row in bindings["owners"].values()}
request_path=BASE/"basics1075-full-literal-source-review-request-v1.json"
new_json(request_path,request)
verify_protected()
print(json.dumps({"status":"canonical_future23_actual_standalone_and_named_pair_passed_no22_mapping","source":CANONICAL,"source_sha256":DIGEST,"request":{"file":relative(request_path),"sha256":sha(request_path)},"actual_records":pairs,"protected_source_count":len(protected),"new_public_theorem_count":6}))
