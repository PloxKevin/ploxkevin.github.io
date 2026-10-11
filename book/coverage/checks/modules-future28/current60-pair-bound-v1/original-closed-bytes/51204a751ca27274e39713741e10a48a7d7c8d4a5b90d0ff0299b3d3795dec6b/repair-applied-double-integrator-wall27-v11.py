from pathlib import Path
import hashlib
p=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v10.lean');s=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()=='abdd2c5c11dc9ba0cfc73c860ade2da6f6222f0b6fa22dfa1ee66b6475f060cf'
a='    rw [Real.volume_real_Ico_of_le (by have hn : 0 ≤ 2*epsilon/Delta^2 := by positivity; linarith : -a ≤ 2*epsilon/Delta^2)] at hh'
b='    have ho : -a ≤ 2*epsilon/Delta^2 := (neg_nonpos.mpr ha.le).trans (by positivity)\n    rw [Real.volume_real_Ico_of_le ho] at hh'
c='  rw [Real.volume_real_Ico_of_le (by have hn : 0 ≤ 2*a*epsilon/(v*min Delta (v/(2*a))) := by positivity; linarith : -a ≤ -a+2*a*epsilon/(v*min Delta (v/(2*a))))] at hh'
d='  have ho : -a ≤ -a+2*a*epsilon/(v*min Delta (v/(2*a))) := le_add_of_nonneg_right (by positivity)\n  rw [Real.volume_real_Ico_of_le ho] at hh'
assert s.count(a)==s.count(c)==1;s=s.replace(a,b).replace(c,d);out=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v11.lean');assert not out.exists();out.write_text(s);print(out,hashlib.sha256(out.read_bytes()).hexdigest())
