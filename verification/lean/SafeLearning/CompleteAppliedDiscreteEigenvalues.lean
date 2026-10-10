import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedDiscreteEigenvalues

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def orbit (T : E→L[ℂ] E) (initial : E) (n : ℕ) : E := (T^[n]) initial

theorem actual_eigenvector_orbit (T : E→L[ℂ] E) (v : E) (eigenvalue : ℂ)
    (he : T v=eigenvalue•v) (n : ℕ) : orbit T v n=eigenvalue^n•v := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
    rw [orbit,Function.iterate_succ_apply']
    change T (orbit T v n)=_
    rw [ih,map_smul,he,smul_smul,pow_succ]

theorem actual_discrete_eigenvalue_magnitude_condition
    (T : E→L[ℂ] E) (v : E) (eigenvalue : ℂ) (hv : v≠0)
    (he : T v=eigenvalue•v)
    (hdecay : Tendsto (orbit T v) atTop (𝓝 0)) : ‖eigenvalue‖<1 := by
  have hnorm : Tendsto (fun n : ℕ=>‖orbit T v n‖) atTop (𝓝 0) := by
    simpa using hdecay.norm
  have hdiv := hnorm.div_const ‖v‖
  have hnonzero : ‖v‖≠0 := norm_ne_zero_iff.mpr hv
  have hp : Tendsto (fun n : ℕ=>‖eigenvalue‖^n) atTop (𝓝 0) := by
    simpa [actual_eigenvector_orbit T v eigenvalue he,norm_smul,norm_pow,hnonzero] using hdiv
  have hlt := tendsto_pow_atTop_nhds_zero_iff.mp hp
  simpa [abs_of_nonneg (norm_nonneg eigenvalue)] using hlt

theorem actual_all_initial_decay_requires_every_eigenvalue_inside_unit_circle
    (T : E→L[ℂ] E) (hdecay : ∀v:E,Tendsto (orbit T v) atTop (𝓝 0))
    (eigenvalue : ℂ) (v : E) (hv : v≠0) (he : T v=eigenvalue•v) :
    ‖eigenvalue‖<1 :=
  actual_discrete_eigenvalue_magnitude_condition T v eigenvalue hv he (hdecay v)

end SafeLearning.CompleteAppliedDiscreteEigenvalues
