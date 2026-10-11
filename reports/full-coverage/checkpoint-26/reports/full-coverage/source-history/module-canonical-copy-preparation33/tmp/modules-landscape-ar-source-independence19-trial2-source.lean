import SafeLearning.CompleteModulesLandscapeARGaussianLaw
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeARSourceIndependence
open CompleteModulesLandscapeARGaussianAlgebra CompleteModulesLandscapeARGaussianLaw

theorem actual_noise_at_or_after_a_time_is_independent_of_the_recursive_state
    (k goal sigma : ℝ) (T s : ℕ) (j : Fin T) (hjs : s ≤ j.val) :
    IndepFun (fun w : Fin T → ℝ => trajectory k goal sigma w s)
      (fun w : Fin T → ℝ => w j) (noiseLaw T) := by
  classical
  let f : Fin T → (Fin T → ℝ) → ℝ := fun i w =>
    if i = j then w i else coefficient k sigma s i.val * w i
  have hf : iIndepFun f (noiseLaw T) := by
    have hnoise := (actual_canonical_noises_are_independent_standard_gaussians T).1
    have h := hnoise.comp
      (fun i : Fin T => fun x : ℝ => if i = j then x else coefficient k sigma s i.val * x)
      (by intro i; by_cases hi : i = j <;> simp [hi] <;> fun_prop)
    simpa only [Function.comp_def] using h
  have hm : ∀ i, Measurable (f i) := by
    intro i
    dsimp [f]
    split_ifs <;> fun_prop
  have hind := hf.indepFun_finsetSum_of_notMem hm
    (s := Finset.univ.erase j) (i := j) (by simp)
  have hz : coefficient k sigma s j.val = 0 := by
    simp [coefficient, not_lt.mpr hjs]
  have he : (fun w : Fin T → ℝ => trueMean k goal s +
      (∑ i ∈ Finset.univ.erase j, f i) w) =
      (fun w : Fin T → ℝ => trajectory k goal sigma w s) := by
    funext w
    rw [actual_recursive_trajectory_is_exactly_the_finite_affine_noise_transformation]
    congr 1
    simp only [Finset.sum_apply]
    calc
      (∑ i ∈ Finset.univ.erase j, f i w) =
          ∑ i ∈ Finset.univ.erase j, coefficient k sigma s i.val * w i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [f, (Finset.mem_erase.mp hi).1]
      _ = ∑ i : Fin T, coefficient k sigma s i.val * w i := by
        have h := Finset.sum_erase_add (Finset.univ : Finset (Fin T))
          (fun i => coefficient k sigma s i.val * w i) (Finset.mem_univ j)
        simpa only [hz, zero_mul, add_zero] using h
  have hshift := hind.comp (measurable_const_add (trueMean k goal s)) measurable_id
  simpa [Function.comp_def, he, f] using hshift

theorem actual_scaled_fresh_noise_is_independent_of_the_recursive_state
    (k goal sigma : ℝ) (T s : ℕ) (j : Fin T) (hjs : s ≤ j.val) :
    IndepFun (fun w : Fin T → ℝ => trajectory k goal sigma w s)
      (fun w : Fin T → ℝ => sigma * w j) (noiseLaw T) := by
  have h := actual_noise_at_or_after_a_time_is_independent_of_the_recursive_state
    k goal sigma T s j hjs
  simpa only [Function.comp_def, id_eq] using
    h.comp measurable_id (show Measurable (fun x : ℝ => sigma * x) by fun_prop)

end SafeLearning.CompleteModulesLandscapeARSourceIndependence
