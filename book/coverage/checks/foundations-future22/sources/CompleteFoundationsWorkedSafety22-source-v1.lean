import SafeLearning.CompleteFoundationsBook

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsWorkedSafety22

theorem actual_compatible_readings_are_the_literal_closed_interval
    (reading allowance : ℝ) :
    {value : ℝ | |value-reading| ≤ allowance} = Icc (reading-allowance) (reading+allowance) := by
  ext value
  simp only [mem_setOf_eq, abs_le, mem_Icc]
  constructor <;>rintro ⟨h1,h2⟩ <;>constructor <;>linarith

theorem actual_failed_interval_containment_has_an_allowed_unsafe_value
    (reading allowance : ℝ) (safe : Set ℝ)
    (hfailed : ¬ Icc (reading-allowance) (reading+allowance) ⊆ safe) :
    ∃ value : ℝ, |value-reading| ≤ allowance ∧ value ∉ safe := by
  have hw := Set.not_subset.mp hfailed
  obtain ⟨value,hvalue,hunsafe⟩ := hw
  refine ⟨value,?_,hunsafe⟩
  rw [←actual_compatible_readings_are_the_literal_closed_interval] at hvalue
  exact hvalue

theorem actual_affine_disturbance_image_is_the_entire_endpoint_interval
    (constant allowance : ℝ) (hallowance : 0 ≤ allowance) :
    (fun disturbance : ℝ => constant+disturbance) '' Icc 0 allowance =
      Icc constant (constant+allowance) := by
  ext value
  constructor
  · rintro ⟨disturbance,h,rfl⟩
    exact ⟨by linarith [h.1],by linarith [h.2]⟩
  · intro h
    exact ⟨value-constant,⟨by linarith [h.1],by linarith [h.2]⟩,by ring⟩

theorem actual_worked_chamber_successor_image_for_every_command (command : ℝ) :
    (fun disturbance : ℝ => (11/10)*(9/2)+command+disturbance) '' Icc 0 (2/5) =
      Icc (99/20+command) (107/20+command) := by
  convert actual_affine_disturbance_image_is_the_entire_endpoint_interval
    ((11/10)*(9/2)+command) (2/5) (by norm_num) using 1 <;>congr 1 <;>ring

theorem actual_source_feedback_has_the_tighter_input_range_and_complete_safe_image
    (state : ℝ) (hstate : state ∈ Icc (0:ℝ) 5) :
    (-9/50)*state ∈ Icc (-9/10:ℝ) 0 ∧ Icc (-9/10:ℝ) 0 ⊆ Icc (-1:ℝ) 0 ∧
      (fun disturbance : ℝ => (11/10)*state+(-9/50)*state+disturbance) '' Icc 0 (2/5) =
        Icc ((23/25)*state) ((23/25)*state+2/5) ∧
      Icc ((23/25)*state) ((23/25)*state+2/5) ⊆ Icc (0:ℝ) 5 := by
  refine ⟨⟨by linarith [hstate.1,hstate.2],by linarith [hstate.1]⟩,?_,?_,?_⟩
  · intro command hc
    exact ⟨by linarith [hc.1],hc.2⟩
  · convert actual_affine_disturbance_image_is_the_entire_endpoint_interval
      ((11/10)*state+(-9/50)*state) (2/5) (by norm_num) using 1 <;>congr 1 <;>ring
  · intro successor hs
    exact ⟨by linarith [hstate.1,hs.1],by linarith [hstate.2,hs.2]⟩

theorem actual_source_feedback_is_safe_at_every_time_with_arbitrary_disturbances
    (state disturbance : ℕ → ℝ) (hinitial : state 0 ∈ Icc (0:ℝ) 5)
    (hdisturbance : ∀ n, disturbance n ∈ Icc (0:ℝ) (2/5))
    (hstep : ∀ n, state (n+1)=(11/10)*state n+(-9/50)*state n+disturbance n) :
    ∀ n, state n ∈ Icc (0:ℝ) 5 := by
  intro n
  induction n with
  | zero =>exact hinitial
  | succ n ih =>
    rw [hstep]
    exact (CompleteFoundationsBook.chamber_nominal_feedback (state n) (disturbance n)
      ih (hdisturbance n)).2

theorem actual_finite_geometric_sum_via_literal_multiplication_cancellation
    (factor : ℝ) (n : ℕ) (hfactor : factor ≠ 1) :
    (∑ j ∈ Finset.range n, factor^j)*(1-factor)=1-factor^n ∧
      (∑ j ∈ Finset.range n, factor^j)=(1-factor^n)/(1-factor) := by
  have h := geom_sum_mul_neg factor n
  exact ⟨h,(eq_div_iff (sub_ne_zero.mpr (Ne.symm hfactor))).mpr h⟩

def sourceEnvelope (n : ℕ) : ℝ := 1/20+3/4*(3/5:ℝ)^n

theorem actual_source_unrolled_sum_equals_the_literal_error_envelope (n : ℕ) :
    (4/5:ℝ)*(3/5)^n+(1/50)*∑ j ∈ Finset.range n, (3/5:ℝ)^j = sourceEnvelope n := by
  rw [(actual_finite_geometric_sum_via_literal_multiplication_cancellation
    (3/5:ℝ) n (by norm_num)).2]
  unfold sourceEnvelope
  ring

theorem actual_source_error_recursion_has_the_literal_every_prefix_bound
    (error : ℕ → ℝ) (hinitial : error 0=4/5)
    (hstep : ∀ n, error (n+1) ≤ (3/5)*error n+1/50) :
    ∀ n, error n ≤ sourceEnvelope n ∧
      error n ≤ (4/5:ℝ)*(3/5)^n+(1/50)*∑ j ∈ Finset.range n, (3/5:ℝ)^j := by
  intro n
  have h := CompleteFoundationsBook.affine_recurrence_envelope error (3/5) (1/50)
    (1/20) (by norm_num) (by norm_num) hstep n
  rw [hinitial] at h
  have he : error n ≤ sourceEnvelope n := by
    unfold sourceEnvelope
    convert h using 1 <;>ring
  exact ⟨he,by rw [actual_source_unrolled_sum_equals_the_literal_error_envelope];exact he⟩

theorem actual_source_first_two_error_bounds
    (error : ℕ → ℝ) (hinitial : error 0=4/5)
    (hstep : ∀ n, error (n+1) ≤ (3/5)*error n+1/50) :
    error 1 ≤ 1/2 ∧ error 2 ≤ 8/25 := by
  have h := actual_source_error_recursion_has_the_literal_every_prefix_bound error hinitial hstep
  constructor
  · have h1 := (h 1).1
    norm_num [sourceEnvelope] at h1
    exact h1
  · have h2 := (h 2).1
    norm_num [sourceEnvelope] at h2
    exact h2

theorem actual_source_tolerance_is_equivalent_to_the_literal_log_cutoff (n : ℕ) :
    (3/4:ℝ)*(3/5)^n ≤ 1/100 ↔ Real.log (1/75:ℝ)/Real.log (3/5:ℝ) ≤ (n:ℝ) := by
  have hlog : Real.log (3/5:ℝ)<0 := Real.log_neg (by norm_num) (by norm_num)
  have hpower : (3/4:ℝ)*(3/5)^n ≤ 1/100 ↔ (3/5:ℝ)^n ≤ 1/75 := by
    constructor <;>intro h <;>linarith
  rw [hpower,div_le_iff_of_neg hlog,
    ←Real.log_le_log_iff (pow_pos (by norm_num : (0:ℝ)<3/5) n) (by norm_num),Real.log_pow]

theorem actual_source_neighboring_certificate_values_and_first_index :
    sourceEnvelope 8=6259712/100000000 ∧ sourceEnvelope 9=57558272/1000000000 ∧
      (∀ n, sourceEnvelope n ≤ 3/50 ↔ 9 ≤ n) ∧ (5:ℕ)+9*2=23 := by
  refine ⟨by norm_num [sourceEnvelope],by norm_num [sourceEnvelope],?_,by norm_num⟩
  exact CompleteFoundationsBook.worked_error_budget

theorem actual_source_finite_envelope_stays_strictly_above_its_floor (n : ℕ) :
    (1/20:ℝ)<sourceEnvelope n ∧ ¬sourceEnvelope n ≤ 1/25 := by
  have hp : (0:ℝ)<(3/5:ℝ)^n := pow_pos (by norm_num) n
  unfold sourceEnvelope
  constructor <;>nlinarith

theorem actual_source_envelope_has_its_true_limit_and_is_an_admitted_equality_trajectory :
    Tendsto sourceEnvelope atTop (𝓝 (1/20:ℝ)) ∧ sourceEnvelope 0=4/5 ∧
      ∀ n, sourceEnvelope (n+1)=(3/5)*sourceEnvelope n+1/50 := by
  refine ⟨?_,by norm_num [sourceEnvelope],?_⟩
  · have hp : Tendsto (fun n : ℕ => (3/5:ℝ)^n) atTop (𝓝 (0:ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have ht := (hp.const_mul (3/4:ℝ)).const_add (1/20:ℝ)
    convert ht using 1 <;>first | rfl | norm_num
  · intro n
    unfold sourceEnvelope
    rw [pow_succ]
    ring

theorem actual_general_affine_error_floor_follows_from_the_finite_geometric_sum
    (error : ℕ → ℝ) (factor additive : ℝ) (hfactor0 : 0 ≤ factor) (hfactor1 : factor<1)
    (hstep : ∀ n, error (n+1) ≤ factor*error n+additive) :
    (∀ n, error n ≤ factor^n*error 0+additive*∑ j ∈ Finset.range n, factor^j) ∧
      Tendsto (fun n : ℕ => factor^n*error 0+additive*∑ j ∈ Finset.range n, factor^j)
        atTop (𝓝 (additive/(1-factor))) := by
  have hne : factor ≠ 1 := ne_of_lt hfactor1
  have hbalance : factor*(additive/(1-factor))+additive=additive/(1-factor) := by
    field_simp [sub_ne_zero.mpr (Ne.symm hne)]
    ring
  have heq (n : ℕ) : factor^n*error 0+additive*∑ j ∈ Finset.range n, factor^j =
      additive/(1-factor)+factor^n*(error 0-additive/(1-factor)) := by
    rw [(actual_finite_geometric_sum_via_literal_multiplication_cancellation factor n hne).2]
    field_simp [sub_ne_zero.mpr (Ne.symm hne)]
    ring
  constructor
  · intro n
    rw [heq]
    exact CompleteFoundationsBook.affine_recurrence_envelope error factor additive
      (additive/(1-factor)) hfactor0 hbalance hstep n
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hfactor0 hfactor1).mul_const
      (error 0-additive/(1-factor)) |>.const_add (additive/(1-factor))
    simpa only [heq,zero_mul,add_zero] using ht

end SafeLearning.CompleteFoundationsWorkedSafety22
