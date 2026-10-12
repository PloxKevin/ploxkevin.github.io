import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteFoundationsPositiveSubunitPNorm32
variable {I : Type*} [Fintype I] [DecidableEq I]

def powerQuasiNorm (p : ℝ) (x : I → ℝ) : ℝ :=
  (∑ i, |x i|^p)^(1/p)

theorem actual_coordinate_unit_has_power_quasinorm_one
    (p : ℝ) (hp : 0 < p) (i : I) : powerQuasiNorm p (Pi.single i (1:ℝ))=1 := by
  have hs : (fun k : I => |(Pi.single i (1:ℝ) : I → ℝ) k|^p)=
      fun k => if k=i then (1:ℝ) else 0 := by
    funext k
    by_cases hi : k=i
    · subst k; simp
    · simp [Pi.single_apply,hi,hi.symm,Real.zero_rpow hp.ne']
  rw [powerQuasiNorm,hs]
  simp

theorem actual_two_distinct_units_have_power_quasinorm_two_to_inverse_p
    (p : ℝ) (hp : 0 < p) (i j : I) (hij : i≠j) :
    powerQuasiNorm p (Pi.single i (1:ℝ)+Pi.single j (1:ℝ))=(2:ℝ)^(1/p) := by
  have hs : (fun k : I => |((Pi.single i (1:ℝ)+Pi.single j (1:ℝ)) : I → ℝ) k|^p)=
      fun k => (if k=i then (1:ℝ) else 0)+(if k=j then (1:ℝ) else 0) := by
    funext k
    by_cases hi : k=i
    · subst k
      simp [Pi.single_apply,hij,hij.symm]
    · by_cases hj : k=j
      · subst k
        simp [Pi.single_apply,hij,hij.symm]
      · simp [Pi.single_apply,hi,hi.symm,hj,hj.symm,Real.zero_rpow hp.ne']
  rw [powerQuasiNorm,hs,Finset.sum_add_distrib]
  simp

theorem actual_every_positive_subunit_exponent_fails_the_triangle_inequality
    [Nontrivial I] (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ x y : I → ℝ,powerQuasiNorm p x+powerQuasiNorm p y < powerQuasiNorm p (x+y) := by
  obtain ⟨i,j,hij⟩:=exists_pair_ne I
  refine ⟨Pi.single i (1:ℝ),Pi.single j (1:ℝ),?_⟩
  rw [actual_coordinate_unit_has_power_quasinorm_one p hp i,
    actual_coordinate_unit_has_power_quasinorm_one p hp j,
    actual_two_distinct_units_have_power_quasinorm_two_to_inverse_p p hp i j hij]
  have hi : (1:ℝ) < 1/p := (lt_div_iff₀ hp).mpr (by linarith)
  have hr : (2:ℝ) < (2:ℝ)^(1/p) := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) hi
  simpa only [one_add_one_eq_two] using hr

theorem actual_printed_half_exponent_values_are_four_versus_one_plus_one :
    powerQuasiNorm (1/2) (![1,1] : Fin 2 → ℝ)=4 ∧
    powerQuasiNorm (1/2) (![1,0] : Fin 2 → ℝ)=1 ∧
    powerQuasiNorm (1/2) (![0,1] : Fin 2 → ℝ)=1 ∧ (2:ℝ) < 4 := by
  norm_num [powerQuasiNorm,Fin.sum_univ_succ]

theorem actual_one_dimensional_positive_power_formula_is_still_absolute_value
    (p : ℝ) (hp : 0 < p) (x : Fin 1 → ℝ) : powerQuasiNorm p x=|x 0| := by
  simp only [powerQuasiNorm,Fin.sum_univ_succ,Finset.univ_eq_empty,Finset.sum_empty,add_zero]
  rw [← Real.rpow_mul (abs_nonneg _) p (1/p)]
  have he : p*(1/p)=1 := by field_simp [hp.ne']
  rw [he,Real.rpow_one]

end SafeLearning.CompleteFoundationsPositiveSubunitPNorm32
