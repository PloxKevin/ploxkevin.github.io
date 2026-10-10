import SafeLearning.CompleteAppliedGlobalLipschitzTrajectory
import SafeLearning.CompleteAppliedGlobalLipschitzACUniqueness

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SafeLearning.CompleteAppliedSmallGainGlobal
open CompleteAppliedGlobalLipschitzTrajectory CompleteAppliedGlobalLipschitzACUniqueness

def sourceField (phi : ℝ → ℝ) (state : ℝ) : ℝ := -state + (4 / 5) * phi state

theorem actual_small_gain_field_is_globally_lipschitz
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) :
    LipschitzWith (9 / 5) (sourceField phi) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp : |phi x - phi y| ≤ |x - y| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hl.dist_le_mul x y
  rw [Real.dist_eq, Real.dist_eq]
  change |sourceField phi x - sourceField phi y| ≤ (9 / 5 : ℝ) * |x - y|
  calc
    _ = |-(x - y) + (4 / 5) * (phi x - phi y)| := by congr 1; unfold sourceField; ring
    _ ≤ |-(x - y)| + |(4 / 5) * (phi x - phi y)| := abs_add_le _ _
    _ = |x - y| + (4 / 5) * |phi x - phi y| := by norm_num [abs_mul, abs_sub_comm]
    _ ≤ (9 / 5 : ℝ) * |x - y| := by linarith

def actualPath (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (initial : ℝ) : ℝ → ℝ :=
  globalSolution (sourceField phi) initial (9 / 5) (actual_small_gain_field_is_globally_lipschitz phi hl)

theorem actual_small_gain_path_has_derived_global_existence_and_ode
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (initial : ℝ) :
    actualPath phi hl initial 0 = initial ∧
      (∀ a b : ℝ, AbsolutelyContinuousOnInterval (actualPath phi hl initial) a b) ∧
        ∀ time : ℝ, HasDerivAt (actualPath phi hl initial)
          (sourceField phi (actualPath phi hl initial time)) time := by
  exact ⟨actual_global_solution_initial_condition _ _ _ _,
    (actual_global_solution_is_c1_and_locally_absolutely_continuous _ _ _ _).2,
    actual_global_solution_has_the_true_ode_at_every_real_time _ _ _ _⟩

theorem actual_small_gain_constructed_global_path_has_the_source_exponential_bound
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0 = 0) (initial time : ℝ)
    (ht : 0 ≤ time) :
    |actualPath phi hl initial time| ≤ |initial| * Real.exp (-(1 / 5) * time) := by
  have hs := actual_small_gain_path_has_derived_global_existence_and_ode phi hl initial
  have hd : ∀ᵐ t ∂volume, t ∈ Icc 0 time →
      HasDerivAt (actualPath phi hl initial) (sourceField phi (actualPath phi hl initial t)) t :=
    Filter.Eventually.of_forall (fun t _ => hs.2.2 t)
  have h := CompleteAppliedSmallGainStorage.actual_source_small_gain_ac_ode_has_the_literal_exponential_bound
    phi hl hz (actualPath phi hl initial) time ht (hs.2.1 0 time) hd time ⟨ht, le_rfl⟩
  simpa only [hs.1] using h

theorem actual_every_finite_ac_small_gain_solution_equals_the_constructed_global_path
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (x : ℝ → ℝ) (initial horizon : ℝ)
    (hT : 0 ≤ horizon) (hc : AbsolutelyContinuousOnInterval x 0 horizon) (hx0 : x 0 = initial)
    (hd : ∀ᵐ time ∂volume, time ∈ Icc 0 horizon → HasDerivAt x (sourceField phi (x time)) time) :
    EqOn x (actualPath phi hl initial) (Icc 0 horizon) := by
  have hs := actual_small_gain_path_has_derived_global_existence_and_ode phi hl initial
  exact actual_globally_lipschitz_field_has_unique_existing_ac_solutions
    (sourceField phi) (9 / 5) (actual_small_gain_field_is_globally_lipschitz phi hl)
    x (actualPath phi hl initial) horizon hT hc (hs.2.1 0 horizon) hd
    (Filter.Eventually.of_forall (fun time _ => hs.2.2 time)) (hx0.trans hs.1.symm)

theorem actual_small_gain_global_path_tends_to_zero_for_every_initial_state
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0 = 0) (initial : ℝ) :
    Tendsto (actualPath phi hl initial) atTop (𝓝 0) := by
  have ht : Tendsto (fun time : ℝ => -(1 / 5) * time) atTop atBot :=
    tendsto_id.const_mul_atTop_of_neg (by norm_num : (-(1 / 5) : ℝ) < 0)
  have he : Tendsto (fun time : ℝ => |initial| * Real.exp (-(1 / 5) * time)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp ht)
  apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
  apply squeeze_zero' (Filter.Eventually.of_forall (fun time => abs_nonneg _)) _ he
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with time ht
  exact actual_small_gain_constructed_global_path_has_the_source_exponential_bound phi hl hz initial time ht

theorem actual_small_gain_origin_has_a_global_exponential_stability_certificate
    (phi : ℝ → ℝ) (hl : LipschitzWith 1 phi) (hz : phi 0 = 0) :
    sourceField phi 0 = 0 ∧ ∀ initial : ℝ, ∃ path : ℝ → ℝ,
      path 0 = initial ∧ (∀ a b : ℝ, AbsolutelyContinuousOnInterval path a b) ∧
      (∀ time : ℝ, HasDerivAt path (sourceField phi (path time)) time) ∧
      (∀ time : ℝ, 0 ≤ time → |path time| ≤ |initial| * Real.exp (-(1 / 5) * time)) ∧
      Tendsto path atTop (𝓝 0) := by
  refine ⟨by simp [sourceField, hz], ?_⟩
  intro initial
  have hs := actual_small_gain_path_has_derived_global_existence_and_ode phi hl initial
  exact ⟨actualPath phi hl initial, hs.1, hs.2.1, hs.2.2,
    fun time ht => actual_small_gain_constructed_global_path_has_the_source_exponential_bound
      phi hl hz initial time ht,
    actual_small_gain_global_path_tends_to_zero_for_every_initial_state phi hl hz initial⟩

end SafeLearning.CompleteAppliedSmallGainGlobal
