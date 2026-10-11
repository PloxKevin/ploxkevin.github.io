import Mathlib

namespace SafeLearning.CompleteCompactLyapunov

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E]

theorem sublevel_forward_invariance (F : E → E) (V : E → ℝ) (x : ℕ → E) (c : ℝ)
    (hF0 : F 0 = 0) (hstep : ∀ n, x (n+1) = F (x n)) (hi : V (x 0) ≤ c)
    (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    ∀ n, V (x n) ≤ c := by
  intro n
  induction n with
  | zero => exact hi
  | succ n ih =>
    rw [hstep]
    by_cases hz : x n = 0
    · simpa [hz, hF0] using ih
    · exact (hdec (x n) ih hz).le.trans ih

theorem trajectory_values_antitone (F : E → E) (V : E → ℝ) (x : ℕ → E) (c : ℝ)
    (hF0 : F 0 = 0) (hstep : ∀ n, x (n+1) = F (x n)) (hi : V (x 0) ≤ c)
    (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    Antitone (fun n => V (x n)) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [hstep]
  by_cases hz : x n = 0
  · simp [hz,hF0]
  · exact (hdec (x n) (sublevel_forward_invariance F V x c hF0 hstep hi hdec n) hz).le

theorem compact_strict_lyapunov_convergence (F : E → E) (V : E → ℝ) (x : ℕ → E)
    (c : ℝ) (hF : Continuous F) (hV : Continuous V)
    (hcompact : IsCompact {y : E | V y ≤ c}) (hnonneg : ∀ y, 0 ≤ V y)
    (hF0 : F 0 = 0) (hstep : ∀ n, x (n+1) = F (x n)) (hi : V (x 0) ≤ c)
    (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    Tendsto x atTop (𝓝 0) := by
  have hinv := sublevel_forward_invariance F V x c hF0 hstep hi hdec
  have hanti := trajectory_values_antitone F V x c hF0 hstep hi hdec
  have hbdd : BddBelow (range (fun n => V (x n))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨n,rfl⟩
    exact hnonneg (x n)
  have hvlimit := tendsto_atTop_ciInf hanti hbdd
  apply hcompact.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall hinv)
  intro a ha hcluster
  obtain ⟨φ,hφ,hsub⟩ := hcluster.tendsto_subseq
  have hVa : V a = ⨅ n, V (x n) :=
    tendsto_nhds_unique (hV.continuousAt.tendsto.comp hsub)
      (hvlimit.comp hφ.tendsto_atTop)
  have hnext : Tendsto (fun n => V (F (x (φ n)))) atTop (𝓝 (⨅ n, V (x n))) := by
    simpa only [Function.comp_def, hstep] using
      hvlimit.comp ((tendsto_add_atTop_nat 1).comp hφ.tendsto_atTop)
  have hVFa : V (F a) = ⨅ n, V (x n) :=
    tendsto_nhds_unique ((hV.comp hF).continuousAt.tendsto.comp hsub) hnext
  by_contra ha0
  have hs := hdec a ha ha0
  linarith

theorem actual_lyapunov_values_converge_to_zero (F : E → E) (V : E → ℝ)
    (x : ℕ → E) (c : ℝ) (hF : Continuous F) (hV : Continuous V)
    (hcompact : IsCompact {y : E | V y ≤ c}) (hnonneg : ∀ y, 0 ≤ V y)
    (hV0 : V 0 = 0) (hF0 : F 0 = 0) (hstep : ∀ n, x (n+1) = F (x n))
    (hi : V (x 0) ≤ c) (hdec : ∀ y, V y ≤ c → y ≠ 0 → V (F y) < V y) :
    Tendsto (fun n => V (x n)) atTop (𝓝 0) := by
  simpa [Function.comp_def, hV0] using hV.continuousAt.tendsto.comp
    (compact_strict_lyapunov_convergence F V x c hF hV hcompact hnonneg hF0 hstep hi hdec)

end SafeLearning.CompleteCompactLyapunov
