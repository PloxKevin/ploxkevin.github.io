import Mathlib

namespace SafeLearning.CompleteLyapunovCounterexample

noncomputable section
open Set Filter
open scoped Topology

def badMap (x : ℝ) : ℝ := if x ≤ 1 then x/2 else (1+x)/2
def orbit (n : ℕ) : ℝ := 1+(1/2 : ℝ)^n
def increment (x : ℝ) : ℝ := (badMap x)^2-x^2
def annulus : Set ℝ := {x | 1 ≤ |x| ∧ |x| ≤ 2}

theorem square_positive_definite :
    (0 : ℝ)^2 = 0 ∧ (∀ x : ℝ, 0 ≤ x^2) ∧ (∀ x : ℝ, x ≠ 0 → 0 < x^2) := by
  exact ⟨by norm_num,sq_nonneg,fun _ hx => sq_pos_of_ne_zero hx⟩

theorem all_square_sublevels_compact (c : ℝ) : IsCompact {x : ℝ | x^2 ≤ c} := by
  apply (isCompact_Icc : IsCompact (Icc (-(|c|+1)) (|c|+1))).of_isClosed_subset
    (isClosed_le (by fun_prop) continuous_const)
  intro x hx
  change x^2 ≤ c at hx
  constructor <;> nlinarith [sq_nonneg (x-1),sq_nonneg (x+1),le_abs_self c,abs_nonneg c]

theorem bad_map_fixes_zero : badMap 0 = 0 := by norm_num [badMap]

theorem strict_square_decrease_everywhere_off_zero (x : ℝ) (hx : x ≠ 0) :
    (badMap x)^2 < x^2 := by
  unfold badMap
  split_ifs with h
  · nlinarith [sq_pos_of_ne_zero hx]
  · have hxp : 1 < x := lt_of_not_ge h
    have hp : 0 < (x-1)*(3*x+1) := mul_pos (by linarith) (by linarith)
    nlinarith

theorem actual_orbit_initial : orbit 0 = 2 := by norm_num [orbit]

theorem actual_orbit_strictly_above_one (n : ℕ) : 1 < orbit n := by
  have hp := pow_pos (by norm_num : (0 : ℝ) < 1/2) n
  unfold orbit
  linarith

theorem actual_orbit_step (n : ℕ) : orbit (n+1) = badMap (orbit n) := by
  have h := actual_orbit_strictly_above_one n
  rw [badMap, if_neg (not_le.mpr h)]
  simp only [orbit,pow_succ]
  ring

theorem actual_orbit_converges_to_one : Tendsto orbit atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1+(1/2 : ℝ)^n) atTop (𝓝 1)
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).const_add 1
  simpa only [add_zero] using hh

theorem actual_images_converge_to_one :
    Tendsto (fun n => badMap (orbit n)) atTop (𝓝 1) := by
  simpa only [Function.comp_def, actual_orbit_step] using
    actual_orbit_converges_to_one.comp (tendsto_add_atTop_nat 1)

theorem actual_orbit_does_not_converge_to_zero : ¬ Tendsto orbit atTop (𝓝 0) := by
  intro h
  have hh := tendsto_nhds_unique actual_orbit_converges_to_one h
  norm_num at hh

theorem actual_map_discontinuous_at_one : ¬ ContinuousAt badMap 1 := by
  intro h
  have hh := tendsto_nhds_unique (h.tendsto.comp actual_orbit_converges_to_one)
    actual_images_converge_to_one
  norm_num [badMap] at hh

theorem actual_orbit_in_annulus (n : ℕ) : orbit n ∈ annulus := by
  have hp : (1/2 : ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h := actual_orbit_strictly_above_one n
  unfold annulus
  rw [mem_setOf_eq, abs_of_pos (by linarith : 0 < orbit n)]
  unfold orbit at *
  constructor <;> linarith

theorem increments_strictly_negative_on_annulus (x : ℝ) (hx : x ∈ annulus) :
    increment x < 0 := by
  have hn : x ≠ 0 := by
    intro hz
    have h := hx.1
    norm_num [hz] at h
  have hd := strict_square_decrease_everywhere_off_zero x hn
  unfold increment
  linarith

theorem actual_annulus_compact : IsCompact annulus := by
  apply (isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  · intro x hx
    exact abs_le.mp hx.2

theorem actual_increment_sequence_converges_to_zero :
    Tendsto (fun n => increment (orbit n)) atTop (𝓝 0) := by
  simpa [increment] using (actual_images_converge_to_one.pow 2).sub
    (actual_orbit_converges_to_one.pow 2)

theorem actual_increment_supremum_is_zero : IsLUB (increment '' annulus) 0 := by
  constructor
  · rintro y ⟨x,hx,rfl⟩
    exact (increments_strictly_negative_on_annulus x hx).le
  · intro b hb
    have hle : ∀ n, increment (orbit n) ≤ b :=
      fun n => hb ⟨orbit n,actual_orbit_in_annulus n,rfl⟩
    exact le_of_tendsto actual_increment_sequence_converges_to_zero (Eventually.of_forall hle)

theorem actual_increment_supremum_not_attained :
    ¬ ∃ x ∈ annulus, increment x = 0 := by
  rintro ⟨x,hx,he⟩
  have h := increments_strictly_negative_on_annulus x hx
  linarith

theorem actual_boundary_increment : increment 1 = -3/4 := by norm_num [increment,badMap]

end
end SafeLearning.CompleteLyapunovCounterexample
