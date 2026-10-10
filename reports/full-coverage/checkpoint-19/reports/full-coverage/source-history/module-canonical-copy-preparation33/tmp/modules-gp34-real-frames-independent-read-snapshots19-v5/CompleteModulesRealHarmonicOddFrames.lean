import SafeLearning.CompleteModulesRealHarmonicPairedFrames
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRealHarmonicOddFrames
open CompleteModulesRealHarmonicOrthogonality CompleteModulesRealHarmonicPairedFrames
variable {n : ℕ} [NeZero n]
variable {K : Type*} [Fintype K] [DecidableEq K]

def oddFrame (f : K → ZMod n) : Matrix (ZMod n) (Unit ⊕ (K × Fin 2)) ℝ :=
  Matrix.of (fun t p => Sum.elim
    (fun _ => Real.sqrt (1/(1+2*(Fintype.card K:ℝ))))
    (fun q => Real.sqrt (2/(1+2*(Fintype.card K:ℝ))) *
      realComponent (characterValue (f q.1) t) q.2) p)

theorem actual_odd_harmonic_inputs_have_unit_euclidean_norm
    (f : K → ZMod n) (t : ZMod n) :
    ‖(WithLp.toLp 2 (fun p => oddFrame f t p) :
      EuclideanSpace ℝ (Unit ⊕ (K × Fin 2)))‖=1 := by
  have hd : (0:ℝ)<1+2*(Fintype.card K:ℝ) := by positivity
  have ha : (Real.sqrt (1/(1+2*(Fintype.card K:ℝ))))^2=
      1/(1+2*(Fintype.card K:ℝ)) := Real.sq_sqrt (by positivity)
  have hb : (Real.sqrt (2/(1+2*(Fintype.card K:ℝ))))^2=
      2/(1+2*(Fintype.card K:ℝ)) := Real.sq_sqrt (by positivity)
  have hn : ‖(WithLp.toLp 2 (fun p => oddFrame f t p) :
      EuclideanSpace ℝ (Unit ⊕ (K × Fin 2)))‖^2=1 := by
    rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_sum_type,Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,oddFrame,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const,Finset.card_univ,Fintype.card_unit,one_smul,realComponent,
      Fin.zero_eta,Fin.isValue,ite_true,Fin.mk_one,one_ne_zero,ite_false]
    calc
      _=(Real.sqrt (1/(1+2*(Fintype.card K:ℝ))))^2+
          ∑ _i : K,2/(1+2*(Fintype.card K:ℝ)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        have he := actual_character_real_imaginary_components_have_unit_energy (f i) t
        nlinarith
      _=1 := by
        rw [ha]
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        field_simp <;> ring
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun p => oddFrame f t p) :
    EuclideanSpace ℝ (Unit ⊕ (K × Fin 2)))]

theorem actual_odd_harmonic_design_has_the_uniform_tight_frame_gram
    (f : K → ZMod n) (hf : Function.Injective f)
    (hplus : ∀ i j,f i+f j≠0) (hzero : ∀ i,f i≠0) :
    (oddFrame f)ᵀ*oddFrame f=
      ((n:ℝ)/(Fintype.card (Unit ⊕ (K × Fin 2)):ℝ)) •
        (1 : Matrix (Unit ⊕ (K × Fin 2)) (Unit ⊕ (K × Fin 2)) ℝ) := by
  have ha : (Real.sqrt (1/(1+2*(Fintype.card K:ℝ))))^2=
      1/(1+2*(Fintype.card K:ℝ)) := Real.sq_sqrt (by positivity)
  have hb : (Real.sqrt (2/(1+2*(Fintype.card K:ℝ))))^2=
      2/(1+2*(Fintype.card K:ℝ)) := Real.sq_sqrt (by positivity)
  have hc : (Fintype.card (Unit ⊕ (K × Fin 2)):ℝ)=
      1+2*(Fintype.card K:ℝ) := by
    simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,Fintype.card_fin,
      Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
    ring
  ext p q
  change (∑ t : ZMod n,oddFrame f t p*oddFrame f t q)=_
  rcases p with u|p <;> rcases q with v|q
  · cases u; cases v
    simp only [oddFrame,Matrix.of_apply,Sum.elim_inl]
    simp only [← pow_two,Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul,ha,
      Matrix.smul_apply,Matrix.one_apply,ite_true,smul_eq_mul,mul_one,hc]
    ring
  · have hz := actual_nonzero_frequency_real_columns_have_zero_sum f hzero q
    have hh : (∑ t : ZMod n,oddFrame f t (Sum.inl u)*oddFrame f t (Sum.inr q))=0 := by
      simp only [oddFrame,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr]
      rw [← Finset.mul_sum]
      rw [← Finset.mul_sum,hz,mul_zero,mul_zero]
    rw [hh]
    simp
  · have hz := actual_nonzero_frequency_real_columns_have_zero_sum f hzero p
    have hh : (∑ t : ZMod n,oddFrame f t (Sum.inr p)*oddFrame f t (Sum.inl v))=0 := by
      simp only [oddFrame,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr]
      simp_rw [mul_comm _ (Real.sqrt (1/(1+2*(Fintype.card K:ℝ))))]
      rw [← Finset.mul_sum,← Finset.mul_sum,hz,mul_zero,mul_zero]
    rw [hh]
    simp
  · have hh : (∑ t : ZMod n,oddFrame f t (Sum.inr p)*oddFrame f t (Sum.inr q))=
        (Real.sqrt (2/(1+2*(Fintype.card K:ℝ))))^2*
        (∑ t : ZMod n,realComponent (characterValue (f p.1) t) p.2*
          realComponent (characterValue (f q.1) t) q.2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      simp only [oddFrame,Matrix.of_apply,Sum.elim_inr]
      ring
    rw [hh,hb,actual_selected_real_imaginary_columns_have_the_exact_orthogonal_sum f hf hplus]
    by_cases hpq : p=q
    · subst q
      simp only [ite_true,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,mul_one,hc]
      field_simp <;> ring
    · simp [hpq]

end SafeLearning.CompleteModulesRealHarmonicOddFrames
