import SafeLearning.CompleteAppliedTemperatureSoftmax
import SafeLearning.CompleteAppliedBellman

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal NNReal Topology
open Set Filter MeasureTheory
namespace SafeLearning.CompleteAppliedSoftBellman
open SafeLearning.CompleteAppliedTemperatureSoftmax SafeLearning.CompleteAppliedBellman

variable {n : ℕ} [NeZero n]

theorem actual_entropy_regularized_objective_changes_by_at_most_the_score_bound
    (scores other : Fin n → ℝ) (temperature bound : ℝ) (law : PMF (Fin n))
    (hscore : ∀ i, |scores i-other i|≤bound) :
    |actualTemperatureObjective scores temperature law-
      actualTemperatureObjective other temperature law|≤bound := by
  have h := finite_mean_difference_bound law scores other bound hscore
  simpa only [actualTemperatureObjective,PMF.integral_eq_sum,smul_eq_mul,
    add_sub_add_right_eq_sub,finiteMean] using h

theorem actual_log_sum_exp_has_the_generic_supremum_difference_bound
    (scores other : Fin n → ℝ) (temperature bound : ℝ) (ht : 0<temperature)
    (hscore : ∀ i, |scores i-other i|≤bound) :
    |actualTemperatureValue scores temperature-actualTemperatureValue other temperature|≤bound := by
  have upper (p q : Fin n → ℝ) (hpq : ∀ i, |p i-q i|≤bound) :
      actualTemperatureValue p temperature≤actualTemperatureValue q temperature+bound := by
    let law := actualTemperatureLaw p temperature
    have hp := (actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
      p temperature ht law).2.mpr rfl
    have hq := (actual_temperature_law_is_the_unique_global_entropy_regularized_optimizer
      q temperature ht law).1
    have hb := (abs_le.mp (actual_entropy_regularized_objective_changes_by_at_most_the_score_bound
      p q temperature bound law hpq)).2
    linarith
  have hu := upper scores other hscore
  have hl := upper other scores (fun i => by simpa only [abs_sub_comm] using hscore i)
  rw [abs_le]
  constructor <;> linarith

def actualSoftBellman {S : Type*} [Fintype S]
    (transition : S → Fin n → PMF S) (reward : S → Fin n → ℝ)
    (discount temperature : ℝ) (value : S → ℝ) (state : S) : ℝ :=
  actualTemperatureValue (fun action => reward state action+
    discount*finiteMean (transition state action) value) temperature

theorem actual_soft_bellman_pointwise_contraction {S : Type*} [Fintype S]
    (transition : S → Fin n → PMF S) (reward : S → Fin n → ℝ)
    (discount temperature bound : ℝ) (hg : 0≤discount) (ht : 0<temperature)
    (value other : S → ℝ) (hv : ∀ s, |value s-other s|≤bound) (state : S) :
    |actualSoftBellman transition reward discount temperature value state-
      actualSoftBellman transition reward discount temperature other state|≤discount*bound := by
  apply actual_log_sum_exp_has_the_generic_supremum_difference_bound _ _ _ _ ht
  intro action
  have hd : reward state action+discount*finiteMean (transition state action) value-
      (reward state action+discount*finiteMean (transition state action) other)=
      discount*(finiteMean (transition state action) value-finiteMean (transition state action) other) := by ring
  rw [hd,abs_mul,abs_of_nonneg hg]
  exact mul_le_mul_of_nonneg_left
    (finite_mean_difference_bound (transition state action) value other bound hv) hg

theorem actual_soft_bellman_is_genuinely_contracting {S : Type*} [Fintype S]
    (transition : S → Fin n → PMF S) (reward : S → Fin n → ℝ)
    (discount : NNReal) (temperature : ℝ) (hg : discount<1) (ht : 0<temperature) :
    ContractingWith discount (actualSoftBellman transition reward discount temperature) := by
  refine ⟨hg,LipschitzWith.of_dist_le_mul ?_⟩
  intro value other
  apply (dist_pi_le_iff (mul_nonneg discount.coe_nonneg dist_nonneg)).mpr
  intro state
  have h := actual_soft_bellman_pointwise_contraction transition reward discount temperature
    (dist value other) discount.coe_nonneg ht value other (fun s => by
      simpa only [Real.dist_eq] using dist_le_pi_dist value other s) state
  simpa only [Real.dist_eq] using h

theorem actual_soft_bellman_fixed_point_exists_is_unique_and_value_iteration_converges
    {S : Type*} [Fintype S]
    (transition : S → Fin n → PMF S) (reward : S → Fin n → ℝ)
    (discount : NNReal) (temperature : ℝ) (hg : discount<1) (ht : 0<temperature)
    (initial : S → ℝ) :
    ∃ fixed : S → ℝ,
      (∀ state,actualSoftBellman transition reward discount temperature fixed state=fixed state) ∧
      Tendsto (fun k : ℕ => (actualSoftBellman transition reward discount temperature)^[k] initial)
        atTop (𝓝 fixed) ∧
      (∀ other : S → ℝ,(∀ state,actualSoftBellman transition reward discount temperature other state=other state) → other=fixed) := by
  have hc := actual_soft_bellman_is_genuinely_contracting transition reward discount temperature hg ht
  obtain ⟨fixed,hfixed,hconv,herror⟩ := hc.exists_fixedPoint initial (edist_ne_top _ _)
  refine ⟨fixed,fun state => congrFun hfixed state,hconv,?_⟩
  intro other ho
  exact hc.fixedPoint_unique' (funext ho) hfixed

theorem actual_soft_bellman_tends_to_the_actual_ordinary_bellman_operator
    {S : Type*} [Fintype S]
    (transition : S → Fin n → PMF S) (reward : S → Fin n → ℝ)
    (discount : ℝ) (value : S → ℝ) :
    Tendsto (fun temperature : ℝ => actualSoftBellman transition reward discount temperature value)
      (𝓝[>] (0:ℝ)) (𝓝 (bellman transition reward discount value)) := by
  apply tendsto_pi_nhds.mpr
  intro state
  simpa only [actualSoftBellman,bellman,
    SafeLearning.CompleteFoundationsExponentialLesson.actualMaximum] using
    (actual_temperature_value_has_the_source_maximum_gap_and_true_zero_temperature_limit
      (fun action => reward state action+discount*finiteMean (transition state action) value)).2

end SafeLearning.CompleteAppliedSoftBellman
