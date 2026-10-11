import json,hashlib,re
from pathlib import Path
old=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v11.lean');new=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v12.lean');assert not new.exists();s=old.read_text()
a='''      have hsafe1 := hYs hnext
      have hsafe2 := hYs hnext2
      fin_cases row'''
b='''      have hsafe1 := hYs hnext
      have hsafe2 := hYs hnext2
      clear hY hYs
      fin_cases row'''
assert s.count(a)==1;s=s.replace(a,b,1)
a='''      | live row col =>
        fin_cases row <;> fin_cases col <;>
          simp [hs, unviableStates, world, kernelStates, slope] at hzero'''
b='''      | live row col =>
        clear hstep hlegal
        fin_cases row <;> fin_cases col <;>
          simp [hs, unviableStates, world, kernelStates, slope] at hzero'''
assert s.count(a)==1;s=s.replace(a,b,1)
def stmts(t):return re.findall(r'^theorem\s+(\w+)(.*?)(?::= by)',t,re.M|re.S)
assert stmts(s)==stmts(old.read_text());new.write_text(s)
print(json.dumps({'source':str(new),'sha256':hashlib.sha256(new.read_bytes()).hexdigest(),'status':'new_static_proof_context_optimization_uncompiled','theorem_statements_unchanged':True,'rationale':'Two finite-grid checks now keep the already extracted one/two-step consequences and discard unused universal transition/availability/invariance hypotheses before simp_all, avoiding repeated expansion of unrelated universal matches.'}))
