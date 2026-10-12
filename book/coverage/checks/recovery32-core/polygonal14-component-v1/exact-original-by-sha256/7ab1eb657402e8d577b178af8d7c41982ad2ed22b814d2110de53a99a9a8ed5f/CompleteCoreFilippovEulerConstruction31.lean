import Mathlib
import SafeLearning.CompleteBarrierFilippovHalfspaces

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
namespace SafeLearning.CompleteCoreFilippovVelocityCompactness30

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

abbrev velocities (μ : Measure E) (F : E → E) (x : E) : Set E :=
  SafeLearning.CompleteBarrierFilippovHalfspaces.velocities μ F x

def CutIndex (μ : Measure E) := {p : ℝ × Set E // 0 < p.1 ∧ μ p.2 = 0}

def hull (F : E → E) (x : E) {μ : Measure E} (i : CutIndex μ) : Set E :=
  closure (convexHull ℝ (F '' (ball x i.val.1 \ i.val.2)))

theorem actual_hull_subset_ball (μ : Measure E) (F : E → E) (x : E)
    (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (i : CutIndex μ) :
    hull F x i ⊆ closedBall (0 : E) M := by
  apply closure_minimal _ isClosed_closedBall
  apply convexHull_min _ (convex_closedBall (0 : E) M)
  rintro v ⟨z, hz, rfl⟩
  simpa only [mem_closedBall, dist_zero_right] using hF z

theorem actual_hull_nonempty (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (x : E) (i : CutIndex μ) : (hull F x i).Nonempty := by
  have hb : 0 < μ (ball x i.val.1) := measure_ball_pos μ x i.property.1
  have hne : (ball x i.val.1 \ i.val.2).Nonempty := by
    by_contra he
    have hs : ball x i.val.1 ⊆ i.val.2 := by
      intro z hz
      by_contra hn
      exact he ⟨z, hz, hn⟩
    have hm := measure_mono (μ := μ) hs
    rw [i.property.2] at hm
    exact (not_lt_of_ge hm) hb
  obtain ⟨z, hz⟩ := hne
  exact ⟨F z, subset_closure (subset_convexHull ℝ _ ⟨z, hz, rfl⟩)⟩

theorem actual_hulls_directed (μ : Measure E) (F : E → E) (x : E) :
    Directed (· ⊇ ·) (hull F x (μ := μ)) := by
  intro i j
  have hn : μ (i.val.2 ∪ j.val.2) = 0 := by
    apply le_antisymm _ zero_le
    simpa only [i.property.2, j.property.2, zero_add] using
      measure_union_le (μ := μ) i.val.2 j.val.2
  let k : CutIndex μ := ⟨(min i.val.1 j.val.1, i.val.2 ∪ j.val.2),
    lt_min i.property.1 j.property.1, hn⟩
  refine ⟨k, ?_, ?_⟩
  · apply closure_mono
    apply convexHull_mono
    apply image_mono
    intro z hz
    exact ⟨(ball_subset_ball (min_le_left _ _) hz.1), fun h => hz.2 (Or.inl h)⟩
  · apply closure_mono
    apply convexHull_mono
    apply image_mono
    intro z hz
    exact ⟨(ball_subset_ball (min_le_right _ _) hz.1), fun h => hz.2 (Or.inr h)⟩

theorem actual_intersection_equals_velocities (μ : Measure E) (F : E → E) (x : E) :
    (⋂ i : CutIndex μ, hull F x i) = velocities μ F x := by
  ext v
  constructor
  · intro hv
    change v ∈ ⋂ (r : ℝ) (_ : 0 < r) (N : Set E) (_ : μ N = 0),
      closure (convexHull ℝ (F '' (ball x r \ N)))
    simp only [mem_iInter] at hv ⊢
    intro r hr N hN
    exact hv ⟨(r, N), hr, hN⟩
  · intro hv
    change v ∈ ⋂ (r : ℝ) (_ : 0 < r) (N : Set E) (_ : μ N = 0),
      closure (convexHull ℝ (F '' (ball x r \ N))) at hv
    simp only [mem_iInter] at hv ⊢
    intro i
    exact hv i.val.1 i.property.1 i.val.2 i.property.2

/-- The essential convexified velocity set is nonempty; existence of an
integral curve is a further theorem, and is not assumed or claimed here. -/
theorem actual_velocity_nonempty [ProperSpace E] (μ : Measure E)
    [μ.IsOpenPosMeasure] (F : E → E) (x : E) (M : ℝ)
    (hF : ∀ z, ‖F z‖ ≤ M) : (velocities μ F x).Nonempty := by
  haveI : Nonempty (CutIndex μ) := ⟨⟨(1, ∅), by norm_num, by simp⟩⟩
  rw [← actual_intersection_equals_velocities]
  apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (hull F x (μ := μ)) (actual_hulls_directed μ F x)
      (actual_hull_nonempty μ F x)
  · intro i
    exact (isCompact_closedBall (0 : E) M).of_isClosed_subset isClosed_closure
      (actual_hull_subset_ball μ F x M hF i)
  · intro i
    exact isClosed_closure

theorem actual_velocity_closed (μ : Measure E) (F : E → E) (x : E) :
    IsClosed (velocities μ F x) := by
  rw [← actual_intersection_equals_velocities]
  exact isClosed_iInter fun i => isClosed_closure

theorem actual_velocity_convex (μ : Measure E) (F : E → E) (x : E) :
    Convex ℝ (velocities μ F x) := by
  rw [← actual_intersection_equals_velocities]
  exact convex_iInter fun i => (convex_convexHull ℝ _).closure

theorem actual_velocity_norm_bound (μ : Measure E) (F : E → E) (x v : E)
    (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (hv : v ∈ velocities μ F x) : ‖v‖ ≤ M := by
  rw [← actual_intersection_equals_velocities] at hv
  let i : CutIndex μ := ⟨(1, ∅), by norm_num, by simp⟩
  have hh := actual_hull_subset_ball μ F x M hF i (mem_iInter.mp hv i)
  simpa only [mem_closedBall, dist_zero_right] using hh

theorem actual_velocity_compact [ProperSpace E] (μ : Measure E) (F : E → E)
    (x : E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) : IsCompact (velocities μ F x) := by
  apply (isCompact_closedBall (0 : E) M).of_isClosed_subset (actual_velocity_closed μ F x)
  intro v hv
  simpa only [mem_closedBall, dist_zero_right] using
    actual_velocity_norm_bound μ F x v M hF hv


/-- Equality away from a null set in a neighborhood gives equality of the
actual essential convexified velocities. The exceptional set is not assumed
measurable; its actual measure is zero. -/
theorem actual_local_velocity_subset (μ : Measure E) (F G : E → E) (x : E)
    (R : ℝ) (N₀ : Set E) (hR : 0 < R) (hN : μ N₀ = 0)
    (hFG : ∀ z ∈ ball x R, z ∉ N₀ → F z = G z) :
    velocities μ F x ⊆ velocities μ G x := by
  intro v hv
  rw [← actual_intersection_equals_velocities] at hv ⊢
  apply mem_iInter.mpr
  intro i
  have hnull : μ (i.val.2 ∪ N₀) = 0 := by
    apply le_antisymm _ zero_le
    simpa only [i.property.2, hN, zero_add] using
      measure_union_le (μ := μ) i.val.2 N₀
  let k : CutIndex μ := ⟨(min i.val.1 R, i.val.2 ∪ N₀),
    lt_min i.property.1 hR, hnull⟩
  have hk := mem_iInter.mp hv k
  have hsub : hull F x k ⊆ hull G x i := by
    apply closure_mono
    apply convexHull_mono
    rintro w ⟨z, hz, rfl⟩
    have hzR : z ∈ ball x R := ball_subset_ball (min_le_right _ _) hz.1
    have hzN : z ∉ N₀ := fun h => hz.2 (Or.inr h)
    refine ⟨z, ⟨ball_subset_ball (min_le_left _ _) hz.1,
      fun h => hz.2 (Or.inl h)⟩, ?_⟩
    exact (hFG z hzR hzN).symm
  exact hsub hk

theorem actual_local_velocity_congr (μ : Measure E) (F G : E → E) (x : E)
    (R : ℝ) (N₀ : Set E) (hR : 0 < R) (hN : μ N₀ = 0)
    (hFG : ∀ z ∈ ball x R, z ∉ N₀ → F z = G z) :
    velocities μ F x = velocities μ G x := by
  apply Subset.antisymm
  · exact actual_local_velocity_subset μ F G x R N₀ hR hN hFG
  · exact actual_local_velocity_subset μ G F x R N₀ hR hN
      (fun z hz hN => (hFG z hz hN).symm)

def boundedRepresentative (F : E → E) (M : ℝ) (z : E) : E :=
  if ‖F z‖ ≤ M then F z else 0

theorem actual_representative_norm_bound (F : E → E) (M : ℝ) (hM : 0 ≤ M)
    (z : E) : ‖boundedRepresentative F M z‖ ≤ M := by
  by_cases hz : ‖F z‖ ≤ M
  · simpa only [boundedRepresentative, if_pos hz] using hz
  · simpa only [boundedRepresentative, if_neg hz, norm_zero] using hM

/-- A local essential bound is converted into an actual globally bounded
representative without changing the original velocity set at the base point. -/
theorem actual_essentially_bounded_velocity_properties [ProperSpace E]
    (μ : Measure E) [μ.IsOpenPosMeasure] (F : E → E) (x : E)
    (R M : ℝ) (N₀ : Set E) (hR : 0 < R) (hM : 0 ≤ M) (hN : μ N₀ = 0)
    (hF : ∀ z ∈ ball x R, z ∉ N₀ → ‖F z‖ ≤ M) :
    (velocities μ F x).Nonempty ∧ IsCompact (velocities μ F x) ∧
      IsClosed (velocities μ F x) ∧ Convex ℝ (velocities μ F x) ∧
      (∀ v ∈ velocities μ F x, ‖v‖ ≤ M) := by
  let G := boundedRepresentative F M
  have hG : ∀ z, ‖G z‖ ≤ M := actual_representative_norm_bound F M hM
  have heq : velocities μ F x = velocities μ G x := by
    apply actual_local_velocity_congr μ F G x R N₀ hR hN
    intro z hz hn
    simp only [G, boundedRepresentative, if_pos (hF z hz hn)]
  refine ⟨?_, ?_, actual_velocity_closed μ F x, actual_velocity_convex μ F x, ?_⟩
  · rw [heq]
    exact actual_velocity_nonempty μ G x M hG
  · rw [heq]
    exact actual_velocity_compact μ G x M hG
  · intro v hv
    rw [heq] at hv
    exact actual_velocity_norm_bound μ G x v M hG hv


open Filter
open scoped Topology

theorem actual_velocity_subset_fixed_hull_nearby (μ : Measure E) (F : E → E)
    (x y : E) (r : ℝ) (N : Set E) (hr : 0 < r) (hN : μ N = 0)
    (hnear : dist y x < r / 2) :
    velocities μ F y ⊆ closure (convexHull ℝ (F '' (ball x r \ N))) := by
  intro v hv
  rw [← actual_intersection_equals_velocities] at hv
  let i : CutIndex μ := ⟨(r / 2, N), by linarith, hN⟩
  have hi := mem_iInter.mp hv i
  apply (show hull F y i ⊆ closure (convexHull ℝ (F '' (ball x r \ N))) from ?_) hi
  apply closure_mono
  apply convexHull_mono
  apply image_mono
  intro z hz
  refine ⟨?_, hz.2⟩
  change dist z x < r
  have hzy : dist z y < r / 2 := hz.1
  have ht := dist_triangle z y x
  linarith

theorem actual_velocity_sequential_closed_graph (μ : Measure E) (F : E → E)
    (xn vn : ℕ → E) (x v : E)
    (hx : Tendsto xn atTop (𝓝 x)) (hv : Tendsto vn atTop (𝓝 v))
    (hm : ∀ n, vn n ∈ velocities μ F (xn n)) :
    v ∈ velocities μ F x := by
  rw [← actual_intersection_equals_velocities]
  apply mem_iInter.mpr
  intro i
  have he : ∀ᶠ n in atTop, dist (xn n) x < i.val.1 / 2 :=
    (Metric.tendsto_nhds.mp hx) (i.val.1 / 2) (by linarith [i.property.1])
  apply isClosed_closure.mem_of_tendsto hv
  filter_upwards [he] with n hn
  exact actual_velocity_subset_fixed_hull_nearby μ F x (xn n) i.val.1 i.val.2
    i.property.1 i.property.2 hn (hm n)

theorem actual_velocity_graph_closed (μ : Measure E) (F : E → E) :
    IsClosed {p : E × E | p.2 ∈ velocities μ F p.1} := by
  apply isSeqClosed_iff_isClosed.mp
  intro sn p hm hp
  exact actual_velocity_sequential_closed_graph μ F
    (fun n => (sn n).1) (fun n => (sn n).2) p.1 p.2
    (continuous_fst.tendsto p |>.comp hp)
    (continuous_snd.tendsto p |>.comp hp) hm


/-- Compact-valued essential convexification is upper hemicontinuous under
an actual global bound; no integral-curve existence is assumed. -/
theorem actual_velocity_upper_hemicontinuous [ProperSpace E]
    (μ : Measure E) (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) :
    UpperHemicontinuous (velocities μ F) := by
  apply UpperHemicontinuous.of_forall_isOpen
  intro x U hU hsub
  let B : Set E := closedBall (0 : E) M
  letI : CompactSpace B := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E) M)
  let bad : Set (E × B) :=
    {p | (p.2 : E) ∈ Uᶜ} ∩ {p | (p.2 : E) ∈ velocities μ F p.1}
  have hproj : Continuous (fun p : E × B => (p.2 : E)) :=
    continuous_subtype_val.comp continuous_snd
  have hpair : Continuous (fun p : E × B => (p.1, (p.2 : E))) :=
    continuous_fst.prodMk hproj
  have hbad : IsClosed bad :=
    (hU.isClosed_compl.preimage hproj).inter
      ((actual_velocity_graph_closed μ F).preimage hpair)
  have hclosed : IsClosed (Prod.fst '' bad) := isClosedMap_fst_of_compactSpace bad hbad
  have hx : x ∈ (Prod.fst '' bad)ᶜ := by
    intro hx
    rcases hx with ⟨p, hp, hpx⟩
    apply hp.1
    apply hsub
    change p.1 = x at hpx
    rw [← hpx]
    exact hp.2
  have he : ∀ᶠ y in 𝓝 x, y ∈ (Prod.fst '' bad)ᶜ := hclosed.isOpen_compl.mem_nhds hx
  filter_upwards [he] with y hy
  intro v hv
  by_contra hvU
  apply hy
  have hb : v ∈ B := by
    simpa only [B, mem_closedBall, dist_zero_right] using actual_velocity_norm_bound μ F y v M hF hv
  exact ⟨(y, ⟨v, hb⟩), ⟨hvU, hv⟩, rfl⟩


/-- Local essential boundedness suffices for upper hemicontinuity at the
base point, by replacing only the out-of-bound values away from its neighborhood. -/
theorem actual_velocity_upper_hemicontinuous_at_of_local_essential_bound [ProperSpace E]
    (μ : Measure E) (F : E → E) (x : E) (R M : ℝ) (N₀ : Set E)
    (hR : 0 < R) (hM : 0 ≤ M) (hN : μ N₀ = 0)
    (hF : ∀ z ∈ ball x R, z ∉ N₀ → ‖F z‖ ≤ M) :
    UpperHemicontinuousAt (velocities μ F) x := by
  let G := boundedRepresentative F M
  have hG : ∀ z, ‖G z‖ ≤ M := actual_representative_norm_bound F M hM
  have he : ∀ᶠ y in 𝓝 x, velocities μ G y = velocities μ F y := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (by linarith : 0 < R / 2))] with y hy
    apply (actual_local_velocity_congr μ F G y (R / 2) N₀ (by linarith) hN ?_).symm
    intro z hz hn
    have hzx : z ∈ ball x R := by
      have hzy : dist z y < R / 2 := hz
      have hyx : dist y x < R / 2 := hy
      have ht := dist_triangle z y x
      change dist z x < R
      linarith
    simp only [G, boundedRepresentative, ite_eq_left (hF z hzx hn)]
  apply upperHemicontinuousWithinAt_univ_iff.mp
  apply (upperHemicontinuousWithinAt_univ_iff.mpr
    ((actual_velocity_upper_hemicontinuous μ G M hG).upperHemicontinuousAt x)).congr_of_eventuallyEq
    (mem_univ x)
  simpa only [nhdsWithin_univ] using he

end SafeLearning.CompleteCoreFilippovVelocityCompactness30


namespace SafeLearning.CompleteCoreFilippovVelocityCompactness30
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [ProperSpace E]

/-- An actual essential-convexified velocity is chosen using the proved
nonemptiness theorem, rather than assuming an integral curve exists. -/
def chosenVelocity (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (x : E) : E :=
  Classical.choose (actual_velocity_nonempty μ F x M hF)

theorem chosenVelocity_mem (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (x : E) :
    chosenVelocity μ F M hF x ∈ velocities μ F x :=
  Classical.choose_spec (actual_velocity_nonempty μ F x M hF)

theorem chosenVelocity_norm_bound (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (x : E) :
    ‖chosenVelocity μ F M hF x‖ ≤ M :=
  actual_velocity_norm_bound μ F x _ M hF (chosenVelocity_mem μ F M hF x)

def eulerNodes (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | n + 1 => eulerNodes μ F M hF h x₀ n +
      h • chosenVelocity μ F M hF (eulerNodes μ F M hF h x₀ n)

theorem actual_euler_initial (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (x₀ : E) :
    eulerNodes μ F M hF h x₀ 0 = x₀ := rfl

theorem actual_euler_increment_is_actual_velocity (μ : Measure E)
    [μ.IsOpenPosMeasure] (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M)
    (h : ℝ) (x₀ : E) (n : ℕ) :
    ∃ v ∈ velocities μ F (eulerNodes μ F M hF h x₀ n),
      eulerNodes μ F M hF h x₀ (n + 1) - eulerNodes μ F M hF h x₀ n = h • v := by
  refine ⟨chosenVelocity μ F M hF _, chosenVelocity_mem μ F M hF _, ?_⟩
  simp only [eulerNodes, add_sub_cancel_left]

theorem actual_euler_increment_bound (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (hh : 0 ≤ h)
    (x₀ : E) (n : ℕ) :
    ‖eulerNodes μ F M hF h x₀ (n + 1) - eulerNodes μ F M hF h x₀ n‖ ≤ h * M := by
  simp only [eulerNodes, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
  exact mul_le_mul_of_nonneg_left (chosenVelocity_norm_bound μ F M hF _) hh

theorem actual_euler_grid_radius_bound (μ : Measure E) [μ.IsOpenPosMeasure]
    (F : E → E) (M : ℝ) (hF : ∀ z, ‖F z‖ ≤ M) (h : ℝ) (hh : 0 ≤ h)
    (x₀ : E) (n : ℕ) : ‖eulerNodes μ F M hF h x₀ n - x₀‖ ≤ (n : ℝ) * h * M := by
  induction n with
  | zero => simp [eulerNodes]
  | succ n ih =>
    have identity : eulerNodes μ F M hF h x₀ (n + 1) - x₀ =
        (eulerNodes μ F M hF h x₀ n - x₀) +
        (eulerNodes μ F M hF h x₀ (n + 1) - eulerNodes μ F M hF h x₀ n) := by abel
    rw [identity]
    calc
      ‖(eulerNodes μ F M hF h x₀ n - x₀) +
        (eulerNodes μ F M hF h x₀ (n + 1) - eulerNodes μ F M hF h x₀ n)‖
        ≤ ‖eulerNodes μ F M hF h x₀ n - x₀‖ +
          ‖eulerNodes μ F M hF h x₀ (n + 1) - eulerNodes μ F M hF h x₀ n‖ := norm_add_le _ _
      _ ≤ (n : ℝ) * h * M + h * M :=
        add_le_add ih (actual_euler_increment_bound μ F M hF h hh x₀ n)
      _ = ((n + 1 : ℕ) : ℝ) * h * M := by push_cast; ring
end SafeLearning.CompleteCoreFilippovVelocityCompactness30
