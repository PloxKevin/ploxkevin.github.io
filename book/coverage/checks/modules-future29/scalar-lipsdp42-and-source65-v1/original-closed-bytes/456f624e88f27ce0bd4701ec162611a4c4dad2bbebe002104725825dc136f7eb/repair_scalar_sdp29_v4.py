from pathlib import Path
s=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v3.lean').read_text()
s=s.replace('LipschitzWith (⟨L,hL⟩ : NNReal) f','LipschitzWith (Real.toNNReal L) f')
s=s.replace('''    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa only [Real.dist_eq,NNReal.coe_mk] using h.2 x y''','''    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Real.dist_eq,Real.toNNReal_of_nonneg hL] using h.2 x y''')
s=s.replace('''    exact ⟨hL,by simpa only [Real.dist_eq,NNReal.coe_mk] using h.dist_le_mul⟩''','''    exact ⟨hL,fun x y=>by
      simpa only [Real.dist_eq,Real.toNNReal_of_nonneg hL] using h.dist_le_mul x y⟩''')
s=s.replace('0<|','0 < |').replace('0≤|','0 ≤ |').replace('|*','| * ')
p=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v4.lean');assert not p.exists();p.write_text(s)
print(len(s.encode()),s.count('\ntheorem '))
