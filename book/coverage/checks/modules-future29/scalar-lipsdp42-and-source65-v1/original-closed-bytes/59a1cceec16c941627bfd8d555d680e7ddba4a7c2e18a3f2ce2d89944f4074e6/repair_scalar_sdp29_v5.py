from pathlib import Path
s=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v4.lean').read_text()
s=s.replace('Real.toNNReal_of_nonneg hL','Real.coe_toNNReal L hL')
s=s.replace('''      exact hn
  have hbdd''','''      simpa only [Real.coe_toNNReal beta hbeta.1] using hn
  have hbdd''')
s=s.replace('''    exact hn


theorem actual_second_derivative''','''    simpa only [Real.coe_toNNReal L hL.1] using hn


theorem actual_second_derivative''')
s=s.replace('add_sub_add_right','add_sub_add_right_eq_sub')
s=s.replace("_ = L*|x-y| := by field_simp [h0.ne'];ring", "_ = L*|x-y| := by field_simp [h0.ne']")
s=s.replace("          field_simp [h0.ne',h1.ne']\n          ring", "          field_simp [h0.ne',h1.ne']")
s=s.replace("    simpa only [mul_div_cancel_left₀ _ hk.ne'] using hs.1", "    simpa only [Set.mem_setOf_eq,mul_div_cancel_left₀ _ hk.ne'] using hs.1")
s=s.replace("    exact (le_div_iff₀ hk).mp (hs.2 hphi)", "    simpa only [mul_comm] using (le_div_iff₀ hk).mp (hs.2 hphi)")
s=s.replace("  rw [mul_comm beta, mul_left_cancel₀ hk]", "  constructor\n  · intro h\n    apply mul_left_cancel₀ hk\n    simpa only [mul_comm beta] using h\n  · intro h\n    rw [h]\n    ring")
s=s.replace("by rw [abs_mul,abs_of_nonneg hb];ring", "by simp only [abs_mul,abs_of_nonneg hb];ring")
p=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v5.lean');assert not p.exists();p.write_text(s)
print(len(s.encode()),s.count('\ntheorem '))
