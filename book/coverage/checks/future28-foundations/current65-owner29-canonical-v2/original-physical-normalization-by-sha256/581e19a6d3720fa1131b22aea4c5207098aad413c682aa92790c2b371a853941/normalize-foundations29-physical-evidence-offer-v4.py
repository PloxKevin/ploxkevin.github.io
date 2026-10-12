from pathlib import Path
from datetime import datetime,timezone
import copy,hashlib,json
R=Path('/home/oxrexkevin/SafetyBased');D=R/'book/coverage/checks/future28-foundations/current65-owner29-canonical-v2'
OLD=D/'foundations29-current65-canonical-offer-draft-v3.json';NEW=D/'foundations29-current65-canonical-offer-draft-v4.json'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def ref(p):return {'file':Path(p).relative_to(R).as_posix(),'sha256':sha(p)}
assert sha(OLD)=='cd6bcd6d9c97d0ab9fc9485043b16dc38e8d7e68cbc88eaaf94498a8a9d28a6d'
o=json.loads(OLD.read_bytes());ctx=json.loads(Path('/tmp/root_tmp_lean_current65_owner28_context_v1.json').read_bytes())
def guard():
 for k in ('pins_sha256','held_current_source_sha256','owners_sha256'):
  for n,h in ctx[k].items():assert sha(R/n)==h,n
 assert sha(OLD)=='cd6bcd6d9c97d0ab9fc9485043b16dc38e8d7e68cbc88eaaf94498a8a9d28a6d'
 for n,h in o['required_evidence_artifacts_sha256'].items():assert sha(R/n)==h,n
guard();aliases={};planned={}
for n,h in o['required_evidence_artifacts_sha256'].items():
 p=R/n
 if p.resolve().is_relative_to(R):continue
 assert n in ['reports/full-coverage/checkpoint-28/verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Lp/PiLp.lean','reports/full-coverage/checkpoint-28/verification/lean/.lake/packages/mathlib/Mathlib/Analysis/Normed/Module/Convex.lean']
 dest=D/'physical-original-dependencies-by-sha256'/h/p.name
 assert not dest.exists();planned[dest]=p.read_bytes();aliases[n]={'file':dest.relative_to(R).as_posix(),'sha256':h}
assert len(aliases)==2
out=copy.deepcopy(o)
for k in ('required_evidence_artifacts_sha256','additional_frozen_inputs'):
 for old,q in aliases.items():
  assert out[k].pop(old)==q['sha256'];assert q['file'] not in out[k];out[k][q['file']]=q['sha256']
for proof in out['proof_files'].values():
 for old,q in aliases.items():
  if old in proof['evidence_sha256']:
   assert proof['evidence_sha256'].pop(old)==q['sha256'];proof['evidence_sha256'][q['file']]=q['sha256']
out['original_physical_containment_draft3']=ref(OLD)
out['original_closed_byte_aliases']=aliases
out['physical_containment_normalization_scope']='Only two immutable evidence-map keys are replaced by physical Root exact-byte copies. Candidate, inverse, semantic decisions, original native bodies and times remain unchanged.'
for k in ('required_evidence_artifacts_sha256','additional_frozen_inputs'):out[k][ref(OLD)['file']]=ref(OLD)['sha256']
assert out['candidate']==o['candidate'] and out['exact_interface']==o['exact_interface']
guard();assert not NEW.exists()
for p,b in planned.items():assert not p.exists() and p.is_relative_to(D)
for p,b in planned.items():p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
NEW.write_text(json.dumps(out,indent=2)+'\n')
guard()
for n,h in out['required_evidence_artifacts_sha256'].items():p=R/n;assert p.resolve().is_relative_to(R) and sha(p)==h,n
print(json.dumps({'status':'passed_exact_two_physical_dependency_alias_normalization','candidate':out['candidate'],'exact_interface':out['exact_interface'],'new_offer':ref(NEW),'aliases':aliases,'required_evidence_count':len(out['required_evidence_artifacts_sha256']),'coverage_complete':False}))
