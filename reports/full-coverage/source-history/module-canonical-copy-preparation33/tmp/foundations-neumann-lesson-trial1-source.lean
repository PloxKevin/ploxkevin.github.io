import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped BigOperators Topology Matrix.Norms.Operator
namespace SafeLearning.CompleteFoundationsNeumannLesson

theorem actual_finite_geometric_left_and_right_cancellation
    {R : Type*} [Ring R] (A : R) (T : ℕ) :
    (1-A)*(∑ t ∈ Finset.range T,A^t)=1-A^T ∧
    (∑ t ∈ Finset.range T,A^t)*(1-A)=1-A^T := by
  constructor
  · simpa only [sub_mul,one_mul,mul_sub,mul_one,neg_sub] using mul_geom_sum_neg A T
  · simpa only [mul_sub,mul_one,neg_sub] using geom_sum_mul_neg A T

theorem actual_geometric_power_operator_bound_and_limit
    {R : Type*} [NormedRing R] [NormOneClass R] (A : R) (hA : ‖A‖<1) :
    (∀ T : ℕ,‖A^T‖≤‖A‖^T) ∧
    Tendsto (fun T : ℕ => ‖A^T‖) atTop (𝓝 0) ∧
    Tendsto (fun T : ℕ => A^T) atTop (𝓝 0) := by
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg A) hA
  have hn := squeeze_zero (fun T=>norm_nonneg (A^T)) (norm_pow_le A) ht
  exact ⟨norm_pow_le A,hn,tendsto_zero_iff_norm_tendsto_zero.mpr hn⟩

theorem actual_neumann_series_true_unit_and_two_sided_inverse
    {R : Type*} [NormedRing R] [CompleteSpace R] (A : R) (hA : ‖A‖<1) :
    IsUnit (1-A) ∧ Summable (fun t : ℕ => A^t) ∧
    HasSum (fun t : ℕ => A^t) (Ring.inverse (1-A)) ∧
    (1-A)*(∑' t : ℕ,A^t)=1 ∧ (∑' t : ℕ,A^t)*(1-A)=1 := by
  exact ⟨isUnit_one_sub_of_norm_lt_one hA,summable_geometric_of_norm_lt_one hA,
    hasSum_geom_series_inverse A hA,mul_neg_geom_series A hA,geom_series_mul_neg A hA⟩

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem actual_stochastic_matrix_true_induced_infinity_norm_is_one
    (P : Matrix S S ℝ) (hP0 : ∀ i j,0≤P i j) (hP1 : ∀ i,∑ j,P i j=1) :
    ‖P‖=1 := by
  rw [Matrix.linfty_opNorm_def]
  have hr : (fun i : S=>∑ j,‖P i j‖)=(fun _ : S=>(1:ℝ)) := by
    funext i
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hP0 i _)] using hP1 i
  rw [hr]
  exact norm_one

theorem actual_discounted_stochastic_matrix_true_induced_infinity_norm
    (P : Matrix S S ℝ) (hP0 : ∀ i j,0≤P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (gamma : ℝ) (hg0 : 0≤gamma) : ‖gamma • P‖=gamma := by
  rw [norm_smul,actual_stochastic_matrix_true_induced_infinity_norm_is_one P hP0 hP1,
    Real.norm_eq_abs,abs_of_nonneg hg0,mul_one]

theorem actual_finite_matrix_neumann_series_is_the_literal_matrix_inverse
    (A : Matrix S S ℝ) (hA : ‖A‖<1) :
    IsUnit (1-A) ∧ HasSum (fun t : ℕ => A^t) ((1-A)⁻¹) ∧
    (1-A)*(∑' t : ℕ,A^t)=1 ∧ (∑' t : ℕ,A^t)*(1-A)=1 := by
  have h := actual_neumann_series_true_unit_and_two_sided_inverse A hA
  exact ⟨h.1,by simpa only [Matrix.nonsing_inv_eq_ringInverse] using h.2.2.1,
    h.2.2.2.1,h.2.2.2.2⟩

theorem actual_discounted_stochastic_matrix_literal_inverse_and_power_series
    (P : Matrix S S ℝ) (hP0 : ∀ i j,0≤P i j) (hP1 : ∀ i,∑ j,P i j=1)
    (gamma : ℝ) (hg0 : 0≤gamma) (hg1 : gamma<1) :
    HasSum (fun t : ℕ => gamma^t • P^t) ((1-gamma • P)⁻¹) ∧
    (∑' t : ℕ,gamma^t • P^t)=(1-gamma • P)⁻¹ := by
  have hn : ‖gamma • P‖<1 := by
    rw [actual_discounted_stochastic_matrix_true_induced_infinity_norm P hP0 hP1 gamma hg0]
    exact hg1
  have h := (actual_finite_matrix_neumann_series_is_the_literal_matrix_inverse (gamma • P) hn).2.1
  have he : (fun t : ℕ => (gamma • P)^t)=(fun t : ℕ => gamma^t • P^t) := by
    funext t
    exact smul_pow gamma P t
  rw [he] at h
  exact ⟨h,h.tsum_eq⟩

end SafeLearning.CompleteFoundationsNeumannLesson
