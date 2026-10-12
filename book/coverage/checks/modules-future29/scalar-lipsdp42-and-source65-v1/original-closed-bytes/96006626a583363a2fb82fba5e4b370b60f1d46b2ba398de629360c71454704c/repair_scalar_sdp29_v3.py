from pathlib import Path
s=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v2.lean').read_text()
s=s.replace('sub_self,zero_pow,mul_zero,\n      one_pow,mul_one,zero_add] at hv','sub_self,\n      one_pow,mul_one] at hv')
s=s.replace('rw [hz,zero_pow,zero_div] at he','simp only [hz,zero_pow (by decide : (2:ℕ)≠0),zero_div] at he')
s=s.replace('''    simp only [objective,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,id_eq]
    ring''','''    simp only [objective,Pi.sub_apply,Pi.div_apply,Pi.pow_apply,id_eq]''')
s=s.replace('(⟨L,hL⟩ : ℝ≥0)','(⟨L,hL⟩ : NNReal)')
s=s.replace('\nend SafeLearning.CompleteModulesScalarLipSDPOptimum29\n','')
s+='''

theorem actual_second_derivative_is_the_genuine_iterated_derivative
    (a beta w1 t : ℝ) (ht : w1^2/2<t) :
    HasDerivAt (deriv (objective a beta w1)) (secondDerivative a beta w1 t) t := by
  have hd : 2*t-w1^2≠0 := by linarith
  apply (actual_first_derivative_has_the_printed_second_derivative a beta w1 t hd).congr_of_eventuallyEq
  exact (lt_mem_nhds ht).mono (fun y hy=>by
    exact (actual_objective_has_the_printed_first_derivative a beta w1 y (by linarith)).deriv)

theorem actual_objective_is_strictly_convex_on_its_entire_feasible_domain
    (a beta w1 : ℝ) (ha : 0≤a) (hab : a<beta) (hw1 : w1≠0) :
    StrictConvexOn ℝ (Ioi (w1^2/2)) (objective a beta w1) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi _) ?_ ?_
  · intro t ht
    exact (actual_objective_has_the_printed_first_derivative a beta w1 t
      (by change w1^2/2<t at ht;linarith)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    change 0<deriv (deriv (objective a beta w1)) t
    rw [(actual_second_derivative_is_the_genuine_iterated_derivative a beta w1 t ht).deriv]
    exact actual_second_derivative_is_strictly_positive a beta w1 t ha hab hw1 ht

theorem actual_normalized_stationary_quadratic_equivalence (a beta s : ℝ) :
    ((a+beta)^2*(s^2-s)=a*beta*(2*s-1)^2) ↔
      (beta-a)^2*(s^2-s)=a*beta := by
  have he : (a+beta)^2*(s^2-s)-a*beta*(2*s-1)^2=
      (beta-a)^2*(s^2-s)-a*beta := by ring
  constructor <;> intro h <;> nlinarith [he]

theorem actual_printed_above_half_root_formula (a beta : ℝ) (hab : a<beta) :
    (1/2:ℝ)*(1+(a+beta)/(beta-a))=beta/(beta-a) := by
  field_simp [sub_ne_zero.mpr (ne_of_gt hab)]
  ring

theorem actual_network_bound_iff_activation_bound
    (phi : ℝ → ℝ) (w0 w1 b c L : ℝ) (hw0 : w0≠0) (hw1 : w1≠0) (hL : 0≤L) :
    realLipschitzBound (scalarNetwork phi w0 w1 b c) L ↔
      realLipschitzBound phi (L/|w0*w1|) := by
  have h0 : 0<|w0| := abs_pos.mpr hw0
  have h1 : 0<|w1| := abs_pos.mpr hw1
  have hk : 0<|w0*w1| := abs_pos.mpr (mul_ne_zero hw0 hw1)
  constructor
  · intro h
    constructor
    · exact div_nonneg hL hk.le
    · intro x y
      have hx : w0*((x-b)/w0)+b=x := by field_simp [hw0];ring
      have hy : w0*((y-b)/w0)+b=y := by field_simp [hw0];ring
      have he : (x-b)/w0-(y-b)/w0=(x-y)/w0 := by ring
      have hd := h.2 ((x-b)/w0) ((y-b)/w0)
      simp only [scalarNetwork,hx,hy,add_sub_add_right,←mul_sub,abs_mul,he,abs_div] at hd
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hk).mpr
      calc
        |phi x-phi y|*|w0*w1|=|w0|*(|w1|*|phi x-phi y|) := by rw [abs_mul];ring
        _ ≤ |w0|*(L*(|x-y|/|w0|)) := mul_le_mul_of_nonneg_left hd h0.le
        _ = L*|x-y| := by field_simp [h0.ne'];ring
  · intro h
    constructor
    · exact hL
    · intro x y
      have hd := h.2 (w0*x+b) (w0*y+b)
      have he : w0*x+b-(w0*y+b)=w0*(x-y) := by ring
      calc
        |scalarNetwork phi w0 w1 b c x-scalarNetwork phi w0 w1 b c y|=
            |w1|*|phi (w0*x+b)-phi (w0*y+b)| := by
              unfold scalarNetwork
              rw [add_sub_add_right,←mul_sub,abs_mul]
        _ ≤ |w1|*((L/|w0*w1|)*|(w0*x+b)-(w0*y+b)|) :=
          mul_le_mul_of_nonneg_left hd h1.le
        _ = L*|x-y| := by
          rw [he,abs_mul,abs_mul]
          field_simp [h0.ne',h1.ne']
          ring

theorem actual_derivative_supremum_gives_the_exact_network_constant
    (phi : ℝ → ℝ) (a beta w0 w1 b c : ℝ) (ha : 0≤a) (hab : a<beta)
    (hp : slopeRestricted phi a beta) (hw0 : w0≠0) (hw1 : w1≠0) :
    IsLeast {L : ℝ | realLipschitzBound (scalarNetwork phi w0 w1 b c) L}
      (|w0*w1|*derivativeSupremum phi) := by
  have hs := actual_derivative_supremum_is_the_least_activation_lipschitz_constant phi a beta ha hab hp
  have hk : 0<|w0*w1| := abs_pos.mpr (mul_ne_zero hw0 hw1)
  constructor
  · have hnon : 0≤|w0*w1|*derivativeSupremum phi := mul_nonneg hk.le hs.1.1
    apply (actual_network_bound_iff_activation_bound phi w0 w1 b c _ hw0 hw1 hnon).mpr
    simpa only [mul_div_cancel_left₀ _ hk.ne'] using hs.1
  · intro L hL
    have hphi := (actual_network_bound_iff_activation_bound phi w0 w1 b c L hw0 hw1 hL.1).mp hL
    exact (le_div_iff₀ hk).mp (hs.2 hphi)

theorem actual_certificate_is_tight_exactly_for_the_activation_own_constant
    (phi : ℝ → ℝ) (beta w0 w1 : ℝ) (hw0 : w0≠0) (hw1 : w1≠0) :
    beta*|w0*w1|=|w0*w1|*derivativeSupremum phi ↔ beta=derivativeSupremum phi := by
  have hk : |w0*w1|≠0 := abs_ne_zero.mpr (mul_ne_zero hw0 hw1)
  rw [mul_comm beta, mul_left_cancel₀ hk]

theorem actual_all_pattern_and_product_constants_equal_the_sdp_constant
    (a beta w0 w1 : ℝ) (ha : 0≤a) (hab : a<beta) :
    IsGreatest {L : ℝ | ∃ s : ℝ,s∈Icc a beta ∧ L=|w0*w1*s|} (beta*|w0*w1|) ∧
      |w1|*beta*|w0|=beta*|w0*w1| := by
  have hb : 0≤beta := by linarith
  constructor
  · constructor
    · exact ⟨beta,⟨hab.le,le_rfl⟩,by rw [abs_mul,abs_of_nonneg hb];ring⟩
    · rintro _ ⟨s,hs,rfl⟩
      rw [abs_mul,abs_of_nonneg (le_trans ha hs.1)]
      nlinarith [mul_le_mul_of_nonneg_left hs.2 (abs_nonneg (w0*w1))]
  · rw [abs_mul]
    ring

theorem actual_supremal_derivative_can_be_attained_or_approached
    (phi : ℝ → ℝ) (a beta : ℝ) (ha : 0≤a) (hab : a<beta)
    (hp : slopeRestricted phi a beta) :
    ∀ eps : ℝ,0<eps → ∃ u : ℝ,derivativeSupremum phi-eps<deriv phi u := by
  intro eps heps
  obtain ⟨s,⟨u,rfl⟩,hu⟩ := exists_lt_of_lt_csSup (Set.range_nonempty (deriv phi))
    (show derivativeSupremum phi-eps<sSup (Set.range (deriv phi)) by
      unfold derivativeSupremum;linarith)
  exact ⟨u,hu⟩

end SafeLearning.CompleteModulesScalarLipSDPOptimum29
'''
p=Path('/tmp/CompleteModulesScalarLipSDPOptimum29-draft-v3.lean')
assert not p.exists()
p.write_text(s)
print(len(s.encode()),s.count('\ntheorem '))
