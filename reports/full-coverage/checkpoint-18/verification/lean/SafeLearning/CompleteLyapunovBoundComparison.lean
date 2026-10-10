import Mathlib

set_option autoImplicit false
noncomputable section
open Filter Set
open scoped Topology

namespace SafeLearning.CompleteLyapunovBoundComparison

def composite (dt : ℝ) : ℝ := 4 + 6 * dt
def smallStep (dt : ℝ) : ℝ := 8 * dt + 6 * dt ^ 2

theorem actual_source_bound_formulas (dt : ℝ) :
    composite dt = 2 * ((1 + dt * 3) + 1) ∧
      smallStep dt = dt * (2 * 1 * (1 + dt * 3) + 2 * 3) := by
  unfold composite smallStep
  constructor <;> ring

theorem actual_source_ratio_and_positive_bounds :
    composite (1 / 100) = 203 / 50 ∧ smallStep (1 / 100) = 403 / 5000 ∧
      composite (1 / 100) / smallStep (1 / 100) = 20300 / 403 ∧
      50 < composite (1 / 100) / smallStep (1 / 100) ∧
      composite (1 / 100) / smallStep (1 / 100) < 51 := by
  norm_num [composite, smallStep]

theorem genuine_all_positive_steps_ratio_divergence (R : ℝ) :
    ∃ epsilon > 0, ∀ dt ∈ Ioo (0 : ℝ) epsilon,
      R < composite dt / smallStep dt := by
  let epsilon : ℝ := 1 / (14 * (|R| + 1))
  have hd : 0 < 14 * (|R| + 1) := by positivity
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have he1 : epsilon ≤ 1 := by
    dsimp [epsilon]
    apply (div_le_one hd).2
    have h := abs_nonneg R
    linarith
  refine ⟨epsilon, he, ?_⟩
  intro dt hdt
  have ht1 : dt ≤ 1 := hdt.2.le.trans he1
  have hsq : dt ^ 2 ≤ dt := by nlinarith [hdt.1]
  have hp : dt * (14 * (|R| + 1)) < 1 := by
    exact (lt_div_iff₀ hd).mp hdt.2
  have hden : 0 < 8 * dt + 6 * dt ^ 2 := by nlinarith [sq_nonneg dt, hdt.1]
  have hcap : 8 * dt + 6 * dt ^ 2 ≤ 14 * dt := by linarith
  have hR : R ≤ |R| + 1 := by linarith [le_abs_self R]
  have hh := mul_le_mul hR hcap hden.le (show 0 ≤ |R| + 1 by positivity)
  unfold composite smallStep
  apply (lt_div_iff₀ hden).2
  nlinarith [hdt.1]

theorem genuine_ratio_tends_to_infinity :
    Tendsto (fun dt : ℝ => composite dt / smallStep dt) (𝓝[>] (0 : ℝ)) atTop := by
  rw [tendsto_atTop]
  intro R
  obtain ⟨epsilon, he, hratio⟩ := genuine_all_positive_steps_ratio_divergence R
  have hpos : ∀ᶠ dt : ℝ in 𝓝[>] (0 : ℝ), 0 < dt := self_mem_nhdsWithin
  have hsmall : ∀ᶠ dt : ℝ in 𝓝[>] (0 : ℝ), dt < epsilon :=
    (eventually_lt_nhds he).filter_mono nhdsWithin_le_nhds
  filter_upwards [hpos, hsmall] with dt hp hs
  exact (hratio dt ⟨hp, hs⟩).le

end SafeLearning.CompleteLyapunovBoundComparison
