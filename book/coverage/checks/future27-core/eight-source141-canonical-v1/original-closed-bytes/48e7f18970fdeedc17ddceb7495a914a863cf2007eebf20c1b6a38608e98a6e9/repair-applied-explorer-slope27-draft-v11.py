import hashlib,re,json
from pathlib import Path
old=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v10.lean'); new=Path('/tmp/CompleteAppliedExplorerSlope27-draft-v11.lean'); assert not new.exists()
s=old.read_text()
assert s.count('open scoped Classical\n')==1
s=s.replace('open Set MeasureTheory\n','open Set MeasureTheory\nopen scoped Classical\n',1)
s=s.replace('/-- The source\'s bound on X_U×U now supplies the actual visited reward bound. -/\nopen scoped Classical\n\n','/-- The source\'s bound on X_U×U now supplies the actual visited reward bound. -/\n',1)
a='''      fin_cases row <;> fin_cases col <;> cases a <;> cases b <;>
        simp_all [safeStates, kernelStates, available, step, cell,
          slope, movedRow, movedCol]'''
b='''      fin_cases row <;> fin_cases col <;>
        simp [slope] at hnonslope <;> cases a <;> cases b <;>
        simp_all [safeStates, kernelStates, available, step, cell,
          slope, movedRow, movedCol]'''
assert s.count(a)==1;s=s.replace(a,b,1)
a='''        cases ha0 : actions 0 <;> cases ha1 : actions 1 <;>
          fin_cases row <;> fin_cases col <;>
          simp_all [unviableStates, world, kernelStates, available,
            step, cell, slope, movedRow, movedCol]'''
b='''        fin_cases row <;> fin_cases col <;>
          simp [hs, unviableStates, world, kernelStates, slope] at hzero <;>
          cases ha0 : actions 0 <;> cases ha1 : actions 1 <;>
          simp_all [unviableStates, world, kernelStates, available,
            step, cell, slope, movedRow, movedCol]'''
assert s.count(a)==1;s=s.replace(a,b,1)
def stmts(t):return re.findall(r'^theorem\s+(\w+)(.*?)(?::= by)',t,re.M|re.S)
assert stmts(s)==stmts(old.read_text());assert len(stmts(s))==42
new.write_text(s)
print(json.dumps({'source':str(new),'sha256':hashlib.sha256(new.read_bytes()).hexdigest(),'theorems':len(stmts(s)),'entire_theorem_statements_unchanged':True,'status':'new_uncompiled_repair','changes':['File-level Classical scope precedes doc comments and survives reopened namespace.','Nonslope cells are eliminated before exhaustive two-action branching in both finite-grid proofs.']}))
