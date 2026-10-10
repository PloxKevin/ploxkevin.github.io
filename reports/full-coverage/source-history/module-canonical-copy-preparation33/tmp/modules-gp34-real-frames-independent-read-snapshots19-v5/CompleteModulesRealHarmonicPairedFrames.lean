import SafeLearning.CompleteModulesRealHarmonicOrthogonality
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRealHarmonicPairedFrames
open CompleteModulesRealHarmonicOrthogonality
variable {n : ℕ} [NeZero n]
variable {K : Type*} [Fintype K] [DecidableEq K]

def realComponent (z : ℂ) (r : Fin 2) : ℝ := if r=0 then z.re else z.im

def pairedFrame (f : K → ZMod n) : Matrix (ZMod n) (K × Fin 2) ℝ :=
  Matrix.of (fun t p => Real.sqrt (1/(Fintype.card K:ℝ))*
    realComponent (characterValue (f p.1) t) p.2)

theorem actual_selected_real_imaginary_columns_have_the_exact_orthogonal_sum
    (f : K → ZMod n) (hf : Function.Injective f)
    (hplus : ∀ i j,f i+f j≠0) (p q : K × Fin 2) :
    (∑ t : ZMod n,realComponent (characterValue (f p.1) t) p.2*
      realComponent (characterValue (f q.1) t) q.2)=
        if p=q then (n:ℝ)/2 else 0 := by
  rcases p with ⟨i,r⟩
  rcases q with ⟨j,s⟩
  have h := actual_real_imaginary_character_pairs_are_orthogonal_with_the_true_half_cardinality
    (f i) (f j) (hplus i j)
  simp only [hf.eq_iff] at h
  fin_cases r <;> fin_cases s
  · simpa [realComponent] using h.1
  · simpa [realComponent] using h.2.2.1
  · simpa [realComponent] using h.2.2.2
  · simpa [realComponent] using h.2.1

theorem actual_nonzero_frequency_real_columns_have_zero_sum
    (f : K → ZMod n) (hzero : ∀ i,f i≠0) (p : K × Fin 2) :
    (∑ t : ZMod n,realComponent (characterValue (f p.1) t) p.2)=0 := by
  have h := actual_nonzero_character_real_and_imaginary_sums_vanish (f p.1) (hzero p.1)
  rcases p with ⟨i,r⟩
  fin_cases r
  · simpa [realComponent] using h.1
  · simpa [realComponent] using h.2

theorem actual_paired_harmonic_inputs_have_unit_euclidean_norm
    [Nonempty K] (f : K → ZMod n) (t : ZMod n) :
    ‖(WithLp.toLp 2 (fun p => pairedFrame f t p) : EuclideanSpace ℝ (K × Fin 2))‖=1 := by
  have hm : (0:ℝ)<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (1/(Fintype.card K:ℝ)))^2=1/(Fintype.card K:ℝ) :=
    Real.sq_sqrt (by positivity)
  have hn : ‖(WithLp.toLp 2 (fun p => pairedFrame f t p) : EuclideanSpace ℝ (K × Fin 2))‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,pairedFrame,Matrix.of_apply,realComponent,
      Fin.zero_eta,Fin.isValue,ite_true,Fin.mk_one,one_ne_zero,ite_false]
    calc
      _=∑ _i : K,1/(Fintype.card K:ℝ) := by
        apply Finset.sum_congr rfl
        intro i _
        have he := actual_character_real_imaginary_components_have_unit_energy (f i) t
        nlinarith
      _=1 := by simp [hm.ne']
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun p => pairedFrame f t p) : EuclideanSpace ℝ (K × Fin 2))]

theorem actual_paired_harmonic_design_has_the_uniform_tight_frame_gram
    [Nonempty K] (f : K → ZMod n) (hf : Function.Injective f)
    (hplus : ∀ i j,f i+f j≠0) :
    (pairedFrame f)ᵀ*pairedFrame f=
      ((n:ℝ)/(Fintype.card (K × Fin 2):ℝ)) • (1 : Matrix (K × Fin 2) (K × Fin 2) ℝ) := by
  have hm : (0:ℝ)<(Fintype.card K:ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (1/(Fintype.card K:ℝ)))^2=1/(Fintype.card K:ℝ) :=
    Real.sq_sqrt (by positivity)
  ext p q
  change (∑ t : ZMod n,pairedFrame f t p*pairedFrame f t q)=_
  have hfactor : (∑ t : ZMod n,pairedFrame f t p*pairedFrame f t q)=
      (Real.sqrt (1/(Fintype.card K:ℝ)))^2*
        (∑ t : ZMod n,realComponent (characterValue (f p.1) t) p.2*
          realComponent (characterValue (f q.1) t) q.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    simp only [pairedFrame,Matrix.of_apply]
    ring
  rw [hfactor,hs,actual_selected_real_imaginary_columns_have_the_exact_orthogonal_sum f hf hplus]
  by_cases hpq : p=q
  · subst q
    simp only [ite_true,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_one,
      Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
    field_simp
  · simp [hpq]

end SafeLearning.CompleteModulesRealHarmonicPairedFrames
