import SafeLearning.CoreAnalysis

namespace SafeLearning.CompleteLyapunovMetricModels

theorem actual_metric_sample_error_upper {X : Type*} [PseudoMetricSpace X]
    (decrease : X → ℝ) (hlipschitz : LipschitzWith 5 decrease)
    (query sample : X) (estimate radius : ℝ)
    (hsample : |decrease sample-estimate| ≤ 1/50)
    (hestimate : estimate ≤ -(3/25)) (hdistance : dist query sample ≤ radius) :
    decrease query ≤ -(1/10)+5*radius := by
  have hu := (abs_le.mp hsample).2
  have hs : decrease sample ≤ -(1/10) := by linarith
  simpa using CoreAnalysis.sampled_upper_certificate decrease 5 hlipschitz
    query sample (-(1/10)) radius hs hdistance

theorem actual_metric_grid_radius_bounds {X : Type*} [PseudoMetricSpace X]
    (decrease : X → ℝ) (hlipschitz : LipschitzWith 5 decrease)
    (query sample : X) (estimate : ℝ)
    (hsample : |decrease sample-estimate| ≤ 1/50) (hestimate : estimate ≤ -(3/25)) :
    (dist query sample ≤ 1/100 → decrease query ≤ -(1/20)) ∧
    (dist query sample ≤ 3/100 → decrease query ≤ 1/20) := by
  constructor <;> intro hd
  · have h := actual_metric_sample_error_upper decrease hlipschitz query sample estimate _
      hsample hestimate hd
    linarith
  · have h := actual_metric_sample_error_upper decrease hlipschitz query sample estimate _
      hsample hestimate hd
    linarith

theorem actual_covered_region_has_strict_decrease {X : Type*} [PseudoMetricSpace X]
    (decrease estimate : X → ℝ) (hlipschitz : LipschitzWith 5 decrease)
    (region grid : Set X)
    (hsample : ∀ sample ∈ grid, |decrease sample-estimate sample| ≤ 1/50)
    (hestimate : ∀ sample ∈ grid, estimate sample ≤ -(3/25))
    (hcover : ∀ query ∈ region, ∃ sample ∈ grid, dist query sample ≤ 1/100) :
    ∀ query ∈ region, decrease query ≤ -(1/20) ∧ decrease query < 0 := by
  intro query hquery
  obtain ⟨sample, hg, hd⟩ := hcover query hquery
  have h := (actual_metric_grid_radius_bounds decrease hlipschitz query sample (estimate sample)
    (hsample sample hg) (hestimate sample hg)).1 hd
  exact ⟨h,by linarith⟩

end SafeLearning.CompleteLyapunovMetricModels
