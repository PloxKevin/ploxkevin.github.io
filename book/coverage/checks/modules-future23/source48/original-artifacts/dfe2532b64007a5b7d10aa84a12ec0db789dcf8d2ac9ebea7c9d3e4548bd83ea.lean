import SafeLearning.CompleteModulesNNActivationPractices22
import Mathlib

open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNCertificateAudit23
noncomputable section
open CompleteModulesNNActivationPractices22

def actualBase : Fin 3 → ℝ := ![0,0,1]
def actualChannel (i : Fin 3) (s : ℝ) : ℝ := shifted (actualBase i) s

theorem actual_three_shifted_channels_and_literal_separating_values :
    actualChannel 0 = actualChannel 1 ∧
      (∀ s,actualChannel 0 s=max s 0) ∧
      (∀ s,actualChannel 2 s=max (s+1) 0-1) ∧
      actualChannel 0 (-1/2)=0 ∧ actualChannel 2 (-1/2)= -1/2 ∧
      actualChannel 0≠actualChannel 2 := by
  refine ⟨by funext s;norm_num [actualChannel,actualBase],?_,?_,?_,?_,?_⟩
  · intro s;simp [actualChannel,actualBase,shifted]
  · intro s;norm_num [actualChannel,actualBase,shifted]
  · norm_num [actualChannel,actualBase,shifted]
  · norm_num [actualChannel,actualBase,shifted]
  · intro h;have he:=congrFun h (-1/2)
    norm_num [actualChannel,actualBase,shifted] at he

theorem actual_equal_shift_group_has_the_true_repeated_channel_constraint (x y : ℝ) :
    0 ≤ 2*(actualChannel 0 x-actualChannel 1 y)*
      ((x-y)-(actualChannel 0 x-actualChannel 1 y)) := by
  have he:=actual_three_shifted_channels_and_literal_separating_values.1
  rw [←he]
  have h:=actual_any_equilibrium_shift_preserves_individual_slope_and_sector 0
  have hx:=SafeLearning.CompleteModulesLipSDP.scalar_slope_quadratic_constraint
    (shifted 0) 0 1 h.2.1 x y
  simpa [actualChannel,actualBase] using hx

theorem actual_all_three_channels_have_valid_diagonal_weighted_constraints
    (lambda v : Fin 3 → ℝ) (hlambda : ∀ i,0≤lambda i) :
    0 ≤ ∑ i,lambda i*(2*actualChannel i (v i)*(v i-actualChannel i (v i))) := by
  apply Finset.sum_nonneg
  intro i hi
  apply mul_nonneg (hlambda i)
  exact (actual_any_equilibrium_shift_preserves_individual_slope_and_sector
    (actualBase i)).2.2 (v i)

theorem actual_repeated_constraint_across_unequal_shift_channels_can_fail :
    2*(actualChannel 0 (-3/5)-actualChannel 2 (-1/2))*
      ((-3/5-(-1/2))-(actualChannel 0 (-3/5)-actualChannel 2 (-1/2))) = -3/5 := by
  norm_num [actualChannel,actualBase,shifted]

theorem actual_all_prefix_iqc_is_true_while_an_individual_sample_is_negative :
    (∀ N,0≤∑ t ∈ Finset.range (N+1),sample literalA t) ∧ sample literalA 1<0 := by
  exact ⟨actual_every_hard_iqc_prefix_is_nonnegative literalA,
    actual_source_half_relation_and_negative_sample.2.2.2.2.2.2.1⟩

/-- The filter history remains an explicit argument of every actual IQC sample.
The hard-IQC premise must hold for that history, including its initial state. -/
theorem actual_summing_dissipation_with_the_hard_iqc_preserves_terminal_storage
    {State : Type*} (filterState : ℕ → State) (iqcSample : State → ℝ)
    (V damping : ℕ → ℝ)
    (hdissipation : ∀ t,V (t+1)-V t+damping t+iqcSample (filterState t)≤0)
    (hhard : ∀ N,0≤∑ t ∈ Finset.range (N+1),iqcSample (filterState t)) (N : ℕ) :
    V (N+1)+(∑ t ∈ Finset.range (N+1),damping t) ≤ V 0 := by
  have hs : V (N+1)-V 0+(∑ t ∈ Finset.range (N+1),damping t)+
      (∑ t ∈ Finset.range (N+1),iqcSample (filterState t))≤0 := by
    induction N with
    | zero => simpa using hdissipation 0
    | succ N ih =>
      rw [Finset.sum_range_succ,Finset.sum_range_succ]
      have hn:=hdissipation (N+1)
      linarith
  linarith [hhard N]

theorem actual_filter_initial_state_cannot_be_silently_discarded :
    (1/2:ℝ)*(1/2-0)=1/4 ∧ (1/2:ℝ)*(1/2-1)= -1/4 := by
  constructor <;> norm_num

/-- An explicit proven quadratic-form perturbation bound below the original
strict margin retains feasibility of the actual perturbed symmetric matrix. -/
theorem actual_proven_matrix_perturbation_below_margin_retains_feasibility
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M E : Matrix ι ι ℝ) (hM : M.IsHermitian) (hE : E.IsHermitian)
    (margin delta : ℝ) (hmargin : delta<margin)
    (hm : ∀ x : ι → ℝ,x ⬝ᵥ (M*ᵥ x)≤-margin*(x ⬝ᵥ x))
    (he : ∀ x : ι → ℝ,x ⬝ᵥ (E*ᵥ x)≤delta*(x ⬝ᵥ x)) :
    (-(M+E)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (hM.add hE).neg
  intro x hx
  simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg,Matrix.add_mulVec,dotProduct_add]
  have hp : 0<x ⬝ᵥ x := by
    simpa only [star_trivial] using dotProduct_star_self_pos_iff.mpr hx
  have hmul:=mul_pos (sub_pos.mpr hmargin) hp
  linarith [hm x,he x]

def scalarStabilityForm (weight : ℝ) : ℝ := weight^2-1

theorem actual_arbitrarily_small_numerical_update_can_change_the_certificate_sign
    (epsilon : ℝ) (hpos : 0<epsilon) (hsmall : epsilon<1) :
    |(1+epsilon/2)-(1-epsilon/2)|=epsilon ∧
      scalarStabilityForm (1-epsilon/2)<0 ∧
      0<scalarStabilityForm (1+epsilon/2) ∧
      scalarStabilityForm (1+epsilon/2)-scalarStabilityForm (1-epsilon/2)=2*epsilon := by
  have hp : 0<epsilon^2 := sq_pos_of_pos hpos
  have hu : epsilon^2<epsilon := by nlinarith
  unfold scalarStabilityForm
  refine ⟨?_,?_,?_,?_⟩
  · rw [show (1+epsilon/2)-(1-epsilon/2)=epsilon by ring,abs_of_pos hpos]
  · nlinarith
  · nlinarith
  · ring

end
end SafeLearning.CompleteModulesNNCertificateAudit23
