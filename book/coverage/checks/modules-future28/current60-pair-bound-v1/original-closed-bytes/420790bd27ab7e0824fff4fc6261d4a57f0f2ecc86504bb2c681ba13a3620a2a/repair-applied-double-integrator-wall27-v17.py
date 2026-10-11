from pathlib import Path
import hashlib
src=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v16.lean');dst=Path('/tmp/CompleteAppliedDoubleIntegratorWall27-draft-v17.lean');assert not dst.exists();s=src.read_text()
a='''    simpa only [holdBrakePosition,pow_two] using
''';b='''    change AbsolutelyContinuousOnInterval (fun t : ℝ =>
      x+v*min t Delta+(u/2)*(min t Delta)^2+(v+u*Delta)*holdBrakeTime a v u Delta t-
        (a/2)*(holdBrakeTime a v u Delta t)^2) 0 T
    simpa only [pow_two] using
''';assert s.count(a)==1;s=s.replace(a,b)
a='''    simpa only [holdZeroPosition,pow_two] using
''';b='''    change AbsolutelyContinuousOnInterval (fun t : ℝ =>
      x+v*min t Delta+(u/2)*(min t Delta)^2+(v+u*Delta)*max (t-Delta) 0) 0 T
    simpa only [pow_two] using
''';assert s.count(a)==1;s=s.replace(a,b)
a='''have hh := brakingTime_hasDeriv_before 1 Delta t (by simpa using hbefore)
      simp only [brakingTime,div_one] at hh''';b='''have hh : HasDerivAt (fun y : ℝ => min y Delta) 1 t := by
        simpa [brakingTime] using brakingTime_hasDeriv_before 1 Delta t (by simpa using hbefore)''';assert s.count(a)==2;s=s.replace(a,b)
a='''have hh := brakingTime_hasDeriv_after 1 Delta t (by simpa using hafter)
      simp only [brakingTime,div_one] at hh''';b='''have hh : HasDerivAt (fun y : ℝ => min y Delta) 0 t := by
        simpa [brakingTime] using brakingTime_hasDeriv_after 1 Delta t (by simpa using hafter)''';assert s.count(a)==2;s=s.replace(a,b)
s=s.replace(':= by field_simp;ring',':= by field_simp <;> ring')
a='''      nlinarith
    have hpref : ∀ t : ℝ, 0 ≤ t → t ≤ Delta → L-epsilon+0*t+(u/2)*t^2 < L := by''';b='''      simp only [zero_add,zero_mul]
      nlinarith [hid]
    have hpref : ∀ t : ℝ, 0 ≤ t → t ≤ Delta → L-epsilon+0*t+(u/2)*t^2 < L := by''';assert s.count(a)==1;s=s.replace(a,b)
a='''      have htail := div_nonneg (sq_nonneg (u*Delta)) (by positivity : 0 ≤ 2*a)
      nlinarith''';b='''      have htail := div_nonneg (sq_nonneg (u*Delta)) (by positivity : 0 ≤ 2*a)
      simp only [zero_add,zero_mul] at hpeak ⊢
      nlinarith''';assert s.count(a)==1;s=s.replace(a,b)
s=s.replace('(by fun_prop : Continuous (wallStoppingBarrier a))','(by unfold wallStoppingBarrier; fun_prop : Continuous (wallStoppingBarrier a))')
s=s.replace('have hc : u+u^2/a ≤ 2*a := by linarith','have hc : u+u^2/a ≤ 2*a := by linarith [hu.2]')
dst.write_text(s);print(dst,hashlib.sha256(dst.read_bytes()).hexdigest(),'uncompiled')
