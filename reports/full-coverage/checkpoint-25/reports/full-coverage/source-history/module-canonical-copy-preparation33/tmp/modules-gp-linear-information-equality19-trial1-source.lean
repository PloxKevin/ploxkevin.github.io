import SafeLearning.CompleteModulesGPLinearInformationDesigns
import SafeLearning.CompleteModulesGPLinearInformationStrictness
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesGPLinearInformationEquality
open CompleteModulesGPLinearInformationBounds CompleteModulesGPLinearInformationDesigns
  CompleteModulesGPLinearInformationStrictness
variable {D T : Type*} [Fintype D] [DecidableEq D] [Fintype T] [DecidableEq T]

theorem actual_strict_log_jensen_equality_requires_every_eigenvalue_to_equal_the_average
    [Nonempty D] (mu : D → ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hmu : ∀ i,0 ≤ mu i)
    (he : (∑ i,Real.log (1+mu i/lambda))=
      (Fintype.card D:ℝ)*Real.log (1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ)))) :
    ∀ i,mu i=(∑ j,mu j)/(Fintype.card D:ℝ) := by
  have hn : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : D,1/(Fintype.card D:ℝ))=1 := by simp [hn.ne']
  have hm : (∑ i,(1/(Fintype.card D:ℝ))*(1+mu i/lambda))=
      1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ)) := by
    simp_rw [mul_add,Finset.sum_add_distrib,mul_one]
    rw [hw,←Finset.mul_sum]
    congr 1
    rw [←Finset.sum_div]
    field_simp
  have hf := strictConcaveOn_log_Ioi.map_sum_eq_iff
    (t:=Finset.univ) (w:=fun _ : D => 1/(Fintype.card D:ℝ))
    (p:=fun i => 1+mu i/lambda) (fun _ _ => by positivity) hw
    (fun i _ => add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg (hmu i) hlambda.le))
  have hew : Real.log (∑ i,(1/(Fintype.card D:ℝ))*(1+mu i/lambda))=
      ∑ i,(1/(Fintype.card D:ℝ))*Real.log (1+mu i/lambda) := by
    rw [hm,←Finset.mul_sum,he]
    field_simp
  simp only [smul_eq_mul] at hf
  have hp := hf.mp hew
  intro i
  have hi := hp i (Finset.mem_univ i)
  rw [hm] at hi
  have harg : mu i/lambda=(∑ j,mu j)/(lambda*(Fintype.card D:ℝ)) := by linarith
  have hd : (∑ j,mu j)/(lambda*(Fintype.card D:ℝ))=
      ((∑ j,mu j)/(Fintype.card D:ℝ))/lambda := by ring
  rw [hd] at harg
  exact (div_left_inj' hlambda.ne').mp harg

theorem actual_nonnegative_spectral_budget_equality_requires_full_trace_and_equal_spectrum
    [Nonempty D] (mu : D → ℝ) (lambda budget : ℝ) (hlambda : 0 < lambda)
    (hmu : ∀ i,0 ≤ mu i) (hbudget : (∑ i,mu i) ≤ budget)
    (he : (∑ i,Real.log (1+mu i/lambda))=
      (Fintype.card D:ℝ)*Real.log (1+budget/(lambda*(Fintype.card D:ℝ)))) :
    (∑ i,mu i)=budget ∧ ∀ i,mu i=budget/(Fintype.card D:ℝ) := by
  have hn : (0:ℝ) < (Fintype.card D:ℝ) := by exact_mod_cast Fintype.card_pos
  have hd := mul_pos hlambda hn
  have hs0 : 0 ≤ ∑ i,mu i := Finset.sum_nonneg (fun i _ => hmu i)
  have hb0 : 0 ≤ budget := hs0.trans hbudget
  have harg : 0 < 1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ)) := by positivity
  have hargb : 0 < 1+budget/(lambda*(Fintype.card D:ℝ)) := by positivity
  have hj := actual_log_jensen_bound_for_every_nonnegative_spectrum mu lambda hlambda hmu
  have hl := Real.log_le_log harg (add_le_add le_rfl ((div_le_div_iff_of_pos_right hd).mpr hbudget))
  have hem : (Fintype.card D:ℝ)*Real.log (1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ)))=
      (Fintype.card D:ℝ)*Real.log (1+budget/(lambda*(Fintype.card D:ℝ))) := by
    apply le_antisymm (mul_le_mul_of_nonneg_left hl hn.le)
    rw [←he]
    exact hj
  have hlog := (mul_left_cancel₀ hn.ne' hem)
  have hinputs := Real.log_injOn_pos harg hargb hlog
  have hs : (∑ i,mu i)=budget := by
    have hdiv : (∑ i,mu i)/(lambda*(Fintype.card D:ℝ))=budget/(lambda*(Fintype.card D:ℝ)) := by linarith
    exact (div_left_inj' hd.ne').mp hdiv
  have hej : (∑ i,Real.log (1+mu i/lambda))=
      (Fintype.card D:ℝ)*Real.log (1+(∑ i,mu i)/(lambda*(Fintype.card D:ℝ))) := by
    rw [hs]
    exact he
  exact ⟨hs,fun i => by simpa only [hs] using
    actual_strict_log_jensen_equality_requires_every_eigenvalue_to_equal_the_average mu lambda hlambda hmu hej i⟩

theorem actual_unit_ball_full_trace_equality_requires_every_input_norm_to_be_one
    (X : Matrix T D ℝ)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1)
    (he : (Xᵀ*X).trace=(Fintype.card T:ℝ)) :
    ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖=1 := by
  rw [actual_design_gram_trace_is_the_sum_of_actual_euclidean_squared_input_norms] at he
  have hsq : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖^2 ≤ (1:ℝ) := by
    intro t
    nlinarith [hX t,norm_nonneg (WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)]
  have he' : (∑ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖^2)=∑ _t : T,(1:ℝ) := by simpa using he
  have hp := (Finset.sum_eq_sum_iff_of_le (fun t (_ : t∈Finset.univ) => hsq t)).mp he'
  intro t
  have ht := hp t (Finset.mem_univ t)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)]

theorem actual_attaining_the_dimension_bound_requires_all_source_eigenvalues_and_input_norms
    [Nonempty D] (X : Matrix T D ℝ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hX : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖ ≤ 1)
    (he : information (Xᵀ*X) lambda=(Fintype.card D:ℝ)/2*
      Real.log (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ)))) :
    (∀ i,(actual_design_gram_is_positive_semidefinite X).isHermitian.eigenvalues i=
      (Fintype.card T:ℝ)/(Fintype.card D:ℝ)) ∧
    (∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖=1) := by
  let hG := actual_design_gram_is_positive_semidefinite X
  have ht := actual_unit_ball_design_has_total_gram_trace_at_most_its_sample_count X hX
  have hsum := hG.isHermitian.trace_eq_sum_eigenvalues.symm
  have heig := hG.eigenvalues_nonneg
  unfold information at he
  rw [actual_positive_semidefinite_logdet_is_the_sum_of_its_true_spectral_logarithms
    _ hG lambda hlambda] at he
  have he' : (∑ i,Real.log (1+hG.isHermitian.eigenvalues i/lambda))=
      (Fintype.card D:ℝ)*Real.log (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ))) := by nlinarith
  have hs := actual_nonnegative_spectral_budget_equality_requires_full_trace_and_equal_spectrum
    hG.isHermitian.eigenvalues lambda (Fintype.card T:ℝ) hlambda heig (by rwa [hsum]) he'
  exact ⟨hs.2,actual_unit_ball_full_trace_equality_requires_every_input_norm_to_be_one X hX
    (hsum.symm.trans hs.1)⟩

theorem actual_gram_has_at_least_dimension_minus_samples_zero_eigenvalues
    (X : Matrix T D ℝ) :
    Fintype.card D-Fintype.card T ≤
      Fintype.card {i // (actual_design_gram_is_positive_semidefinite X).isHermitian.eigenvalues i=0} := by
  classical
  have hr := actual_design_gram_rank_is_at_most_the_number_of_samples X
  rw [(actual_design_gram_is_positive_semidefinite X).isHermitian.rank_eq_card_non_zero_eigs] at hr
  have hz := Fintype.card_subtype_compl (fun i =>
    (actual_design_gram_is_positive_semidefinite X).isHermitian.eigenvalues i≠0)
  simp only [not_not] at hz
  rw [hz]
  omega

end SafeLearning.CompleteModulesGPLinearInformationEquality
