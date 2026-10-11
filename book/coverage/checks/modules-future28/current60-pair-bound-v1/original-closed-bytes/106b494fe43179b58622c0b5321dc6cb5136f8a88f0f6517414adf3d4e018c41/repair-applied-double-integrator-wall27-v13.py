from pathlib import Path
import hashlib
p=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v12.lean');s=p.read_text();assert hashlib.sha256(p.read_bytes()).hexdigest()=='b9c9e5208afd9020dd77c689440acdd259c5e23d8bfc5535f13d043bbd1829ec'
a='    exact (((hc.fun_add (hh.const_mul v)).fun_add ((hh.fun_mul hh).const_mul (u/2))).fun_add\n      (hq.const_mul (v+u*Delta))).fun_sub ((hq.fun_mul hq).const_mul (a/2))'
b='    simpa only [holdBrakePosition,pow_two] using\n      (((hc.fun_add (hh.const_mul v)).fun_add ((hh.fun_mul hh).const_mul (u/2))).fun_add\n        (hq.const_mul (v+u*Delta))).fun_sub ((hq.fun_mul hq).const_mul (a/2))'
assert s.count(a)==1;s=s.replace(a,b)
a='    · have hh := brakingTime_hasDeriv_before 1 Delta t (by simpa using hbefore)\n';b=a+'      simp only [brakingTime,div_one] at hh\n';assert s.count(a)==1;s=s.replace(a,b)
a='    · have hh := brakingTime_hasDeriv_after 1 Delta t (by simpa using hafter)\n';b=a+'      simp only [brakingTime,div_one] at hh\n';assert s.count(a)==1;s=s.replace(a,b)
out=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v13.lean');assert not out.exists();out.write_text(s);print(out,hashlib.sha256(out.read_bytes()).hexdigest())
