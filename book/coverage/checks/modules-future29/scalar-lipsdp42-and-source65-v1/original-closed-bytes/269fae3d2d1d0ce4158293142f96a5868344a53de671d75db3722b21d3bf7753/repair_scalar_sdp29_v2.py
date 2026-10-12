from pathlib import Path
p=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v1.lean')
s=p.read_text()
s=s.replace('field_simp [ht]\n  ring','field_simp [ht,show t*2-w1^2≠0 by simpa only [mul_comm] using ht]\n  ring')
s=s.replace('''    simpa only [Matrix.cons_val_zero,Matrix.cons_val_one,sub_self,zero_pow,mul_zero,
      one_pow,mul_one,zero_add] using hv''','''    simp only [Matrix.cons_val_zero,Matrix.cons_val_one,sub_self,zero_pow,mul_zero,
      one_pow,mul_one,zero_add] at hv
    norm_num at hv
    linarith''')
s=s.replace('''      rw [hz,zero_pow,zero_div] at he
      linarith''','''      rw [hz,zero_pow,zero_div] at he
      rw [h]
      linarith''')
s=s.replace('''  convert h using 1 <;> dsimp [objective,firstDerivative]
  · field_simp [ht]
    ring
  · ext x
    ring''','''  convert h using 1
  · ext x
    simp only [objective,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    ring
  · dsimp [firstDerivative]
    field_simp [ht,show t*2-w1^2≠0 by simpa only [mul_comm] using ht]
    ring''')
s=s.replace('''  convert h using 1 <;> dsimp [firstDerivative,secondDerivative]
  · field_simp [ht]
    ring
  · ext x
    ring''','''  convert h using 1
  · ext x
    simp only [firstDerivative,Pi.mul_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    ring
  · dsimp [secondDerivative]
    field_simp [ht,show t*2-w1^2≠0 by simpa only [mul_comm] using ht]
    ring''')
s=s.replace('''  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs))
    (pow_pos (abs_pos.mpr hw1) 4 |>.trans_eq (by simp))) (pow_pos hd 3)''','''  have h4 : 0<w1^4 := by nlinarith [sq_pos_of_ne_zero (pow_ne_zero 2 hw1)]
  exact div_pos (mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hs)) h4) (pow_pos hd 3)''')
s=s.replace('LipschitzWith ⟨L,hL⟩ f','LipschitzWith (⟨L,hL⟩ : ℝ≥0) f')
p2=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v2.lean')
assert not p2.exists()
p2.write_text(s)
print(len(s.encode()))
