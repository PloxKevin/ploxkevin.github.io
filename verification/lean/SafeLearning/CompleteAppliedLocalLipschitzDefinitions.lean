import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedLocalLipschitzDefinitions

variable {X Y : Type*} [MetricSpace X] [ProperSpace X] [PseudoMetricSpace Y]

theorem actual_local_lipschitz_on_open_domain_iff_every_compact_subset
    (domain : Set X) (f : X→Y) (hopen : IsOpen domain) :
    LocallyLipschitzOn domain f ↔
      ∀K:Set X,IsCompact K→K⊆domain→∃L:ℝ≥0,LipschitzOnWith L f K := by
  constructor
  · intro h K hc hs
    exact (h.mono hs).exists_lipschitzOnWith_of_compact hc
  · intro h x hx
    obtain ⟨radius,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
    have hsubset : closedBall x (radius/2)⊆domain := by
      intro y hy
      exact hball ((mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (half_lt_self hr))))
    obtain ⟨L,hL⟩ := h (closedBall x (radius/2)) (isCompact_closedBall x _) hsubset
    exact ⟨L,closedBall x (radius/2),
      mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (half_pos hr)),hL⟩

theorem actual_global_domain_local_lipschitz_iff_every_bounded_set
    (f : X→Y) :
    LocallyLipschitz f ↔
      ∀K:Set X,Bornology.IsBounded K→∃L:ℝ≥0,LipschitzOnWith L f K := by
  constructor
  · intro h K hb
    obtain ⟨L,hL⟩ :=
      h.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hb.isCompact_closure
    exact ⟨L,hL.mono subset_closure⟩
  · intro h
    apply locallyLipschitzOn_univ.mp
    apply (actual_local_lipschitz_on_open_domain_iff_every_compact_subset univ f isOpen_univ).mpr
    intro K hc _
    exact h K hc.isBounded

/-- No actual neighborhood of zero admits a Lipschitz constant for sqrt(abs x). -/
theorem actual_sqrt_abs_is_not_lipschitz_on_any_neighborhood_of_zero
    (neighborhood : Set ℝ) (hn : neighborhood∈𝓝 (0:ℝ)) :
    ¬∃L:ℝ≥0,LipschitzOnWith L (fun x:ℝ=>Real.sqrt |x|) neighborhood := by
  rintro ⟨L,hL⟩
  obtain ⟨radius,hr,hball⟩ := Metric.mem_nhds_iff.mp hn
  let t : ℝ := min (Real.sqrt radius/2) (1/((L:ℝ)+1))
  have ht : 0<t := lt_min (half_pos (Real.sqrt_pos.mpr hr)) (by positivity)
  have hts : t≤Real.sqrt radius/2 := min_le_left _ _
  have htl : t≤1/((L:ℝ)+1) := min_le_right _ _
  have htr : t^2<radius := by
    have hs := Real.sq_sqrt hr.le
    have hp := Real.sqrt_pos.mpr hr
    nlinarith
  have hx : t^2∈neighborhood := by
    apply hball
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (sq_nonneg t)]
    exact htr
  have hz : (0:ℝ)∈neighborhood := hball (mem_ball_self hr)
  have hineq := hL.dist_le_mul (t^2) hx 0 hz
  simp only [Real.dist_eq,abs_of_nonneg (sq_nonneg t),Real.sqrt_sq ht.le,
    abs_zero,Real.sqrt_zero,sub_zero,abs_of_pos ht] at hineq
  have hlt : (L:ℝ)*t<1 := by
    have hm := (le_div_iff₀ (by positivity : 0<(L:ℝ)+1)).mp htl
    nlinarith
  have hpositive := mul_pos ht (sub_pos.mpr hlt)
  nlinarith

theorem actual_reciprocal_is_locally_lipschitz_on_the_positive_domain :
    LocallyLipschitzOn (Ioi (0:ℝ)) (fun x:ℝ=>1/x) := by
  have hc : ContDiffOn ℝ 1 (fun x:ℝ=>x⁻¹) (Ioi 0) :=
    (contDiffOn_inv (𝕜:=ℝ) (𝕜':=ℝ) (n:=1)).mono (fun x hx=>by simpa using ne_of_gt hx)
  simpa only [one_div] using hc.locallyLipschitzOn (convex_Ioi (0:ℝ))

theorem actual_reciprocal_is_not_lipschitz_on_the_bounded_open_unit_interval :
    ¬∃L:ℝ≥0,LipschitzOnWith L (fun x:ℝ=>1/x) (Ioo (0:ℝ) 1) := by
  rintro ⟨L,hL⟩
  let x : ℝ := 1/((L:ℝ)+4)
  have hxpositive : 0<x := by dsimp [x];positivity
  have hxhalf : x<1/2 := by
    dsimp [x]
    apply (div_lt_iff₀ (by positivity : 0<(L:ℝ)+4)).mpr
    linarith [L.coe_nonneg]
  have hx : x∈Ioo (0:ℝ) 1 := ⟨hxpositive,by linarith⟩
  have h := hL.dist_le_mul x hx (1/2) (by norm_num)
  have hinvx : 1/x=(L:ℝ)+4 := by dsimp [x];field_simp
  rw [Real.dist_eq,Real.dist_eq,hinvx] at h
  norm_num only at h
  rw [abs_of_pos (by linarith [L.coe_nonneg] : 0<(L:ℝ)+4-2),
    abs_of_neg (by linarith : x-1/2<0)] at h
  have hm : (L:ℝ)*x≥0 := mul_nonneg L.coe_nonneg hxpositive.le
  nlinarith

theorem actual_open_unit_interval_is_bounded_but_not_compact :
    Bornology.IsBounded (Ioo (0:ℝ) 1) ∧ ¬IsCompact (Ioo (0:ℝ) 1) := by
  constructor
  · exact (isBounded_Icc (a:=(0:ℝ)) (b:=1)).subset Ioo_subset_Icc_self
  · intro hc
    have h0 : (0:ℝ)∈closure (Ioo (0:ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
      norm_num
    rw [hc.isClosed.closure_eq] at h0
    norm_num at h0

end SafeLearning.CompleteAppliedLocalLipschitzDefinitions
