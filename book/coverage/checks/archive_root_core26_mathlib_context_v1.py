"""Close two exact primary-library context files; these are not proof modules."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
CONTEXTS={'verification/lean/.lake/packages/mathlib/Mathlib/Probability/CDF.lean':'78586bddc289a171cbcb7fa155892333c4702c4f7f1185f9d6602ffac8b914e9',
 'verification/lean/.lake/packages/mathlib/Mathlib/MeasureTheory/Measure/Regular.lean':'e2da9c2a5d8874cf2397cc98c114d678fc648e74d62d96c58ed546bcacdaa6be'}
BASE=ROOT/'book/coverage/checks/future26-core/composed-source53-v3/original-primary-mathlib-context'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in CONTEXTS.items():assert (ROOT/n).is_file() and sha(ROOT/n)==h
assert not BASE.exists();BASE.mkdir();aliases=[]
for n,h in CONTEXTS.items():
 p=BASE/Path(n).name
 with p.open('xb') as f:f.write((ROOT/n).read_bytes())
 assert sha(p)==h
 aliases.append({'original':{'file':n,'sha256':h},'immutable_original_byte_copy':{'file':str(p.relative_to(ROOT)),'sha256':h}})
p=BASE/'closed-original-byte-aliases-v1.json'
with p.open('x') as f:f.write(json.dumps({'status':'passed_exact_two_primary_mathlib_context_byte_closure','closed_at_utc':datetime.now(timezone.utc).isoformat(),'aliases':aliases,'scope':'Two source contexts read by the original review are copied exactly. They are historical library evidence, not selected SafeLearning proof sources or new compiler executions.'},indent=2)+'\n')
print(json.dumps({'status':'passed','catalogue':{'file':str(p.relative_to(ROOT)),'sha256':sha(p)}}))
