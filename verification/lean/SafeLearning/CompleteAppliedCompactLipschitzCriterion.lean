import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedCompactLipschitzCriterion

variable {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]

/-- The converse constructs a genuine compact subset from two sequences
witnessing the failure of every local constant. The domain need not be open. -/
theorem actual_local_lipschitz_on_any_domain_iff_every_compact_subset
    (domain : Set X) (f : X→Y) :
    LocallyLipschitzOn domain f ↔
      ∀K:Set X,IsCompact K→K⊆domain→∃L:ℝ≥0,LipschitzOnWith L f K := by
  classical
  constructor
  · intro h K hc hs
    exact (h.mono hs).exists_lipschitzOnWith_of_compact hc
  · intro h x hx
    by_contra hn
    have hpairs : ∀n:ℕ,∃y z:X,y∈domain ∧ z∈domain ∧
        dist y x<1/((n:ℝ)+1) ∧ dist z x<1/((n:ℝ)+1) ∧
        (n:ℝ)*dist y z<dist (f y) (f z) := by
      intro n
      let neighborhood : Set X := domain∩ball x (1/((n:ℝ)+1))
      have hnot : ¬LipschitzOnWith (n:ℝ≥0) f neighborhood := by
        intro hL
        apply hn
        exact ⟨n,neighborhood,inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity))),hL⟩
      rw [lipschitzOnWith_iff_dist_le_mul] at hnot
      push_neg at hnot
      obtain ⟨y,hy,z,hz,hbad⟩ := hnot
      exact ⟨y,z,hy.1,hz.1,hy.2,hz.2,by simpa using hbad⟩
    choose y z hy hz hyd hzd hbad using hpairs
    have hyT : Tendsto y atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _=>dist_nonneg) (fun n=>(hyd n).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    have hzT : Tendsto z atTop (𝓝 x) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      exact squeeze_zero (fun _=>dist_nonneg) (fun n=>(hzd n).le)
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
    let K : Set X := insert x (range y)∪insert x (range z)
    have hcompact : IsCompact K := hyT.isCompact_insert_range.union hzT.isCompact_insert_range
    have hsubset : K⊆domain := by
      apply union_subset
      · exact insert_subset_iff.mpr ⟨hx,range_subset_iff.mpr hy⟩
      · exact insert_subset_iff.mpr ⟨hx,range_subset_iff.mpr hz⟩
    obtain ⟨L,hL⟩ := h K hcompact hsubset
    obtain ⟨n,hn⟩ := exists_nat_gt (L:ℝ)
    have hyK : y n∈K := Or.inl (Or.inr (mem_range_self n))
    have hzK : z n∈K := Or.inr (Or.inr (mem_range_self n))
    have hb := hL.dist_le_mul (y n) hyK (z n) hzK
    have hne : y n≠z n := by
      intro heq
      have hbadn := hbad n
      simp [heq] at hbadn
    have hm := mul_lt_mul_of_pos_right hn (dist_pos.mpr hne)
    linarith [hbad n]

end SafeLearning.CompleteAppliedCompactLipschitzCriterion
