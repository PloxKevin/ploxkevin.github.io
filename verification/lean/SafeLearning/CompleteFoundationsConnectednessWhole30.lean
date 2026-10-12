import Mathlib

set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsConnectednessWhole30
/- Exact primary sine-curve proof body copied from Mathlib Counterexamples/TopologistsSineCurve.lean.
Copyright (c) 2025 Daniele Bolla. Released under Apache 2.0 license.
Authors: Daniele Bolla, David Loeffler. Only the local namespace is renamed.
No counterexample conclusion is supplied as a hypothesis. -/
open Topology Filter Set Real

namespace SineCounterexample

/-- The topologist's sine curve, i.e. the graph of `y = sin (x⁻¹)` for `0 < x`. -/
noncomputable def S : Set (ℝ × ℝ) := (fun x ↦ (x, sin x⁻¹)) '' Ioi 0

/-- The vertical line segment `{ (0, y) | -1 ≤ y ≤ 1 }`, which is the set of limit points of `S`
not contained in `S` itself. -/
def Z : Set (ℝ × ℝ) := (fun y ↦ (0, y)) '' Icc (-1) 1

/-- The union of `S` and `Z` (which we will show is the closure of `S`). -/
noncomputable def T : Set (ℝ × ℝ) := S ∪ Z

/-- A sequence of `x`-values tending to 0 at which the sine curve has a given `y`-coordinate. -/
noncomputable def xSeq (y : ℝ) (k : ℕ) := 1 / (arcsin y + (k + 1) * (2 * π))

lemma xSeq_pos (y : ℝ) (k : ℕ) : 0 < xSeq y k := by
  rw [xSeq, one_div_pos]
  nlinarith [pi_pos, neg_pi_div_two_le_arcsin y]

lemma sin_inv_xSeq {y : ℝ} (hy : y ∈ Icc (-1) 1) (k : ℕ) : sin (xSeq y k)⁻¹ = y := by
  simpa [xSeq, -Nat.cast_add, ← Nat.cast_succ] using sin_arcsin' hy

lemma xSeq_tendsto (y : ℝ) : Tendsto (xSeq y) atTop (𝓝 0) := by
  refine .comp (g := fun k : ℝ ↦ 1 / (arcsin y + (k + 1) * (2 * π))) ?_ tendsto_natCast_atTop_atTop
  simp only [div_eq_mul_inv, show 𝓝 0 = 𝓝 (1 * (0 : ℝ)) by simp]
  refine (tendsto_inv_atTop_zero.comp <| tendsto_atTop_add_const_left _ _ ?_).const_mul _
  exact (tendsto_atTop_add_const_right _ _ tendsto_id).atTop_mul_const (by positivity)

/-!
## `T` is closed
-/

/-- The closure of the topologist's sine curve `S` is the set `T`. -/
lemma closure_S : closure S = T := by
  ext ⟨x, y⟩
  -- Use sequential characterization of closure.
  simp only [mem_closure_iff_seq_limit, Prod.tendsto_iff]
  constructor
  · -- Show that if a sequence in `S` has a limit in `ℝ ^ 2`, the limit must be in `T`.
    rintro ⟨f, hf_mem, hf_lim⟩
    have x_nonneg : 0 ≤ x := by
      refine isClosed_Ici.mem_of_tendsto hf_lim.1 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa [← hy.2] using le_of_lt hy.1
    -- Case split on whether limit point `(x, y)` has `x = 0`.
    rcases x_nonneg.eq_or_lt with rfl | h
    · -- If the limit has `x = 0`, show `y`-coord must be in `[-1, 1]` using closedness
      right
      simp only [Z, mem_image, Prod.mk.injEq, true_and, exists_eq_right]
      refine isClosed_Icc.mem_of_tendsto hf_lim.2 (.of_forall fun n ↦ ?_)
      obtain ⟨y, hy⟩ := hf_mem n
      simpa only [Function.comp_apply, ← hy.2] using sin_mem_Icc ..
    · -- If the limit has `0 < x`, show `y`-coord must be `sin x⁻¹` using continuity
      refine .inl ⟨x, h, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      have : ContinuousAt (fun x ↦ sin x⁻¹) x :=
        continuous_sin.continuousAt.comp <| continuousAt_inv₀ h.ne'
      refine tendsto_nhds_unique_of_forall (this.tendsto.comp hf_lim.1) hf_lim.2 fun n ↦ ?_
      obtain ⟨y, hy⟩ := hf_mem n
      simp [← hy.2]
  · -- Show that every `p ∈ T` is the limit of a sequence in `S`.
    rintro (hz | ⟨z, hz⟩)
    · -- Point is in `S`: use constant sequence
      exact ⟨_, fun _ ↦ hz, tendsto_const_nhds, tendsto_const_nhds⟩
    · -- Point is in `Z`: use sequence from `xSeq`
      simp only [Prod.mk.injEq] at hz
      rcases hz with ⟨hz, ⟨rfl, rfl⟩⟩
      refine ⟨fun n ↦ (xSeq z n, z), fun n ↦ ⟨_, xSeq_pos z n, ?_⟩, xSeq_tendsto z,
        tendsto_const_nhds⟩
      simpa using sin_inv_xSeq hz n

lemma isClosed_T : IsClosed T := by simpa only [← closure_S] using isClosed_closure

/-!
## `T` is connected
-/

/-- `T` is connected, being the closure of the set `S` (which is obviously connected since it
is a continuous image of the positive real line). -/
theorem isConnected_T : IsConnected T := by
  rw [← closure_S]
  refine (isConnected_Ioi.image _ <| continuousOn_id.prodMk ?_).closure
  fun_prop (discharger := grind)

/-!
## `T` is not path-connected
-/

lemma zero_mem_T : (0, 0) ∈ T := by
  refine .inr ⟨0, ⟨?_, ?_⟩, rfl⟩ <;>
  linarith

/-- A point in the `body` of the topologist's sine curve. -/
noncomputable def w : ℝ × ℝ := (1, sin 1⁻¹)

lemma w_mem_T : w ∈ T := .inl ⟨1, ⟨zero_lt_one' ℝ, rfl⟩⟩

private lemma norm_ge_abs_snd {a b : ℝ} : |b| ≤ ‖(a, b)‖ := by simp

private lemma exists_unitInterval_gt {t₀ : unitInterval} (ht₀ : t₀ < 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
  let s₀ := (t₀ : ℝ) -- t₀ is in unitInterval
  let s₁ := min (s₀ + δ / 2) 1
  have h_s₀_delta_pos : 0 ≤ s₀ + δ / 2 := add_nonneg t₀.2.1 (by positivity)
  have hs₁ : 0 ≤ s₁ := le_min h_s₀_delta_pos zero_le_one
  have hs₁' : s₁ ≤ 1 := min_le_right ..
  refine ⟨⟨s₁, hs₁, hs₁'⟩, lt_min ((lt_add_iff_pos_right _).mpr (half_pos hδ)) ht₀, ?_⟩
  have h_le : s₁ ≤ s₀ + δ / 2 := min_le_left _ _
  have h_ge : s₀ ≤ s₁ := le_min (by linarith) t₀.2.2
  rw [Subtype.dist_eq, dist_comm, dist_eq, abs_of_nonneg (by linarith)]
  linarith

private lemma mem_S_of_x_pos {p : ℝ × ℝ} (hx : 0 < p.1) (hT : p ∈ T) : p.2 = sin (p.1)⁻¹ := by
  obtain ⟨x, -, hx⟩ : p ∈ S := by
    cases hT with
    | inl hT => trivial
    | inr hZ => obtain ⟨y, ⟨-, rfl⟩⟩ := hZ; exact (lt_irrefl _ hx).elim
  simp [← hx]

/-- For any `0 < a` and any `y ∈ Icc (-1) 1`, we can find `x ∈ Ioc a 0` with `sin x⁻¹ = y`. -/
lemma exists_mem_Ioc_of_y {y : ℝ} (hy : y ∈ Icc (-1) 1) {a : ℝ} (ha : 0 < a) :
    ∃ x ∈ Ioc 0 a, sin x⁻¹ = y := by
  obtain ⟨N, h_dist⟩ := (Metric.tendsto_nhds.mp (xSeq_tendsto y) (a / 2) (by positivity)).exists
  refine ⟨xSeq y N, ⟨xSeq_pos y N, ?_⟩, sin_inv_xSeq hy _⟩
  rw [dist_eq, sub_zero, abs_of_pos (xSeq_pos _ N)] at h_dist
  linarith

/-- The set `T` is not path-connected. -/
theorem not_isPathConnected_T : ¬ IsPathConnected T := by
  -- **Step 1**:
  -- Assume for contradiction we have a path from `z = (0, 0)` to `w = (1, sin 1)`.
  -- Let t₀ be the last time the path is on the y-axis. By continuity of the path, we
  -- can find a `δ > 0` such that for all `t ∈ [t₀, t₀ + δ]`, we have `‖p(t) - p(t₀)‖ < 1`.
  intro h_pathConn
  replace h_pathConn := h_pathConn.joinedIn (0, 0) zero_mem_T w w_mem_T
  let p := h_pathConn.somePath
  have xcoord_pathContinuous : Continuous fun t ↦ (p t).1 := continuous_fst.comp p.continuous
  let t₀ : unitInterval := sSup {t | (p t).1 = 0}
  have h_pt₀_x : (p t₀).1 = 0 :=
    (isClosed_singleton.preimage xcoord_pathContinuous).sSup_mem ⟨0, by aesop⟩
  obtain ⟨δ, hδ, ht⟩ : ∃ δ, 0 < δ ∧ ∀ t, dist t t₀ < δ → dist (p t) (p t₀) < 1 :=
    Metric.eventually_nhds_iff.mp <| Metric.tendsto_nhds.mp (p.continuousAt t₀) _ one_pos
  -- **Step 2**:
  -- Choose a time t₁ in (t₀, t₀ + δ) and let `a = x(p(t₁))`. Using the fact that every
  -- connected subset of `ℝ` is an interval, we have `[0, a] ⊂ x(p([t0, t1]))`.
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, t₀ < t₁ ∧ dist t₀ t₁ < δ := by
    refine exists_unitInterval_gt (lt_of_le_of_ne (unitInterval.le_one t₀) fun ht₀' ↦ ?_) hδ
    have w_x_path : (p 1).1 = 1 := by rw [Path.target p, w]
    have x_eq_zero : (p 1).1 = 0 := by rwa [ht₀'] at h_pt₀_x
    linarith
  let a := (p t₁).1
  have ha : 0 < a := by
    obtain ⟨x, hxI, hx_eq⟩ : p t₁ ∈ S := by
      refine (h_pathConn.somePath_mem t₁).elim id fun ⟨y, hy⟩ ↦ ?_
      have : (p t₁).1 = 0 := by simp only [p, ← hy.2]
      exact ((show t₁ ≤ t₀ from le_sSup this).not_gt ht₁.1).elim
    simpa only [a, ← hx_eq] using! hxI
  have intervalAZeroSubOfT₀T₁Xcoord : Icc 0 a ⊆ (fun t ↦ (p t).1) '' Icc t₀ t₁ :=
    (isPreconnected_Icc.image _ <| xcoord_pathContinuous.continuousOn).Icc_subset
      (show 0 ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₀, ⟨le_rfl, ht₁.1.le⟩, ‹_›⟩)
      (show a ∈ (fun t ↦ (p t).1) '' Icc t₀ t₁ from ⟨t₁, ⟨ht₁.1.le, le_rfl⟩, rfl⟩)
  -- **Step 3**: For every `y ∈ [-1, 1]`, there exists a `t` with `p t = y` and `dist t₀ t < δ`.
  have exists_close {y : ℝ} (hy : y ∈ Icc (-1) 1) : ∃ t, dist t t₀ < δ ∧ (p t).2 = y := by
    -- first find a `t ∈ [t₀, t₁]` with this property
    obtain ⟨x, hx, hx'⟩ := exists_mem_Ioc_of_y hy ha
    obtain ⟨t, ht⟩ : ∃ t ∈ Icc t₀ t₁, (p t).1 = x := intervalAZeroSubOfT₀T₁Xcoord ⟨hx.1.le, hx.2⟩
    have hp : (p t).2 = sin (p t).1⁻¹ := mem_S_of_x_pos (ht.2 ▸ hx.1) (h_pathConn.somePath_mem t)
    refine ⟨t, ?_, by rw [← hx', hp, ht.2]⟩
    calc -- now show `t ∈ Icc t₀ t₁` implies `dist t t₀ < δ`
    dist t t₀ ≤ dist t₁ t₀ := dist_right_le_of_mem_uIcc (Icc_subset_uIcc' ht.1)
    _ = dist t₀ t₁ := by rw [dist_comm]
    _ < δ := ht₁.2
  -- **Step 4**:
  -- Now the final contradiction: there are times within `δ` of `t₀` with `p t = 1`, and with
  -- `p t = -1`; but both must have distance `< 1` from `p t₀`, contradicting the triangle
  -- inequality.
  obtain ⟨x₁, hx₁, h_pathx₁⟩ : ∃ x₁, dist x₁ t₀ < δ ∧ (p x₁).2 = 1 := exists_close (by simp)
  obtain ⟨x₂, hx₂, h_pathx₂⟩ : ∃ x₂, dist x₂ t₀ < δ ∧ (p x₂).2 = -1 := exists_close (by simp)
  have : dist (p x₁) (p x₂) < 2 := by
    refine (dist_triangle_right _ _ (p t₀)).trans_lt ?_
    exact (add_lt_add (ht _ hx₁) (ht _ hx₂)).trans_eq (by norm_num)
  have := norm_ge_abs_snd.trans_lt this
  rw [h_pathx₁, h_pathx₂, abs_of_nonneg (by norm_num)] at this
  linarith

end SineCounterexample

open Set Topology

/-- The source's pairwise formulation permits the empty set; Mathlib's nonempty convention
is identified explicitly instead of being silently inserted into the literal. -/
def sourcePairwisePathConnected {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ x∈A, ∀ y∈A, ∃ p : Path x y, ∀ t, p t∈A

theorem actual_literal_pairwise_path_definition {X : Type*} [TopologicalSpace X] (A : Set X) :
    sourcePairwisePathConnected A ↔ ∀ x∈A,∀ y∈A,JoinedIn A x y := Iff.rfl

theorem actual_nonempty_path_connected_definition {X : Type*} [TopologicalSpace X] (A : Set X) :
    IsPathConnected A ↔ A.Nonempty ∧ sourcePairwisePathConnected A := isPathConnected_iff

theorem actual_path_component_is_maximal {X : Type*} [TopologicalSpace X]
    (A : Set X) (x : X) (hx : x∈A) :
    x∈pathComponentIn A x ∧ pathComponentIn A x⊆A ∧
    IsPathConnected (pathComponentIn A x) ∧
    ∀ B : Set X,x∈B→B⊆A→IsPathConnected B→B⊆pathComponentIn A x := by
  refine ⟨mem_pathComponentIn_self hx,pathComponentIn_subset,
    isPathConnected_pathComponentIn hx,?_⟩
  intro B hxB hBA hB
  exact hB.subset_pathComponentIn hxB hBA

theorem actual_every_maximal_path_connected_subset_is_a_component
    {X : Type*} [TopologicalSpace X] (A B : Set X) (hB : IsPathConnected B)
    (hBA : B⊆A)
    (hmax : ∀ C : Set X,B⊆C→C⊆A→IsPathConnected C→C=B) :
    ∃x∈B,B=pathComponentIn A x := by
  obtain ⟨x,hx⟩:=hB.nonempty
  refine ⟨x,hx,?_⟩
  exact (hmax _ (hB.subset_pathComponentIn hx hBA) pathComponentIn_subset
    (isPathConnected_pathComponentIn (hBA hx))).symm

theorem actual_open_euclidean_connected_iff_path_connected {I : Type*} [Fintype I]
    (A : Set (I→ℝ)) (hA : IsOpen A) : IsConnected A↔IsPathConnected A :=
  hA.isConnected_iff_isPathConnected

theorem actual_open_euclidean_components_coincide {I : Type*} [Fintype I]
    (A : Set (I→ℝ)) (hA : IsOpen A) (x : I→ℝ) (hx : x∈A) :
    pathComponentIn A x=connectedComponentIn A x := by
  letI : LocallyPathConnectedSpace A := hA.locallyPathConnectedSpace
  rw [connectedComponentIn_eq_image hx]
  ext y
  constructor
  · intro hxy
    have hy:=hxy.target_mem
    refine ⟨⟨y,hy⟩,?_,rfl⟩
    rw [←pathComponent_eq_connectedComponent]
    exact hxy.joined_subtype
  · rintro ⟨y,hy,rfl⟩
    rw [←pathComponent_eq_connectedComponent] at hy
    obtain ⟨p⟩:=hy
    exact ⟨p.map continuous_subtype_val,fun t=>(p t).property⟩

theorem actual_continuous_path_connected_image {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (A : Set X)
    (hA : IsPathConnected A) (f : X→Y) (hf : ContinuousOn f A) :
    IsPathConnected (f '' A) := hA.image' hf

theorem actual_continuous_euclidean_parameterization_has_one_component
    {I Y : Type*} [Fintype I] [TopologicalSpace Y]
    (f : (I→ℝ)→Y) (hf : Continuous f) (A : Set Y) (hinto : ∀u,f u∈A) :
    Set.range f⊆pathComponentIn A (f 0) := by
  have hdomain : IsPathConnected (Set.univ : Set (I→ℝ)) :=
    convex_univ.isPathConnected ⟨0,mem_univ 0⟩
  have h := hdomain.image hf
  rw [Set.image_univ] at h
  exact h.subset_pathComponentIn ⟨0,rfl⟩ (Set.range_subset_iff.mpr hinto)

theorem actual_distinct_components_cannot_both_be_parameterized
    {I Y : Type*} [Fintype I] [TopologicalSpace Y]
    (f : (I→ℝ)→Y) (hf : Continuous f) (A : Set Y) (hinto : ∀u,f u∈A)
    (x y : Y) (hxy : ¬JoinedIn A x y) : ¬(x∈Set.range f ∧ y∈Set.range f) := by
  rintro ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩
  have h:=actual_continuous_euclidean_parameterization_has_one_component f hf A hinto
  exact hxy ((h ⟨u,rfl⟩).symm.trans (h ⟨v,rfl⟩))

theorem actual_connected_components_need_not_be_path_components :
    IsConnected SineCounterexample.T ∧
    pathComponentIn SineCounterexample.T (0,0) ≠
      connectedComponentIn SineCounterexample.T (0,0) := by
  refine ⟨SineCounterexample.isConnected_T,?_⟩
  intro heq
  have h:=isPathConnected_pathComponentIn SineCounterexample.zero_mem_T
  rw [heq,SineCounterexample.isConnected_T.isPreconnected.connectedComponentIn
    SineCounterexample.zero_mem_T] at h
  exact SineCounterexample.not_isPathConnected_T h

theorem actual_continuous_path_in_a_finite_grid_is_constant
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (G : Set X) (hG : G.Finite) (p : C(unitInterval,X)) (hp : ∀t,p t∈G) :
    ∀s t,p s=p t := by
  intro s t
  by_contra hst
  have hrange : (Set.range p).Finite := hG.subset (Set.range_subset_iff.mpr hp)
  have hinfinite : (Set.range p).Infinite :=
    (isConnected_range p.continuous).isPreconnected.infinite_of_nontrivial
      ⟨p s,⟨s,rfl⟩,p t,⟨t,rfl⟩,hst⟩
  exact hrange.not_infinite hinfinite

theorem actual_no_path_joins_distinct_finite_grid_points
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (G : Set X) (hG : G.Finite) (x y : X) (hxy : x≠y) : ¬JoinedIn G x y := by
  rintro ⟨p,hp⟩
  have h:=actual_continuous_path_in_a_finite_grid_is_constant G hG p.toContinuousMap hp 0 1
  exact hxy (by simpa using h)

theorem actual_finite_grid_path_components_are_singletons
    {X : Type*} [TopologicalSpace X] [T1Space X]
    (G : Set X) (hG : G.Finite) (x : X) (hx : x∈G) :
    pathComponentIn G x={x} := by
  ext y
  constructor
  · intro hy
    by_contra h
    exact actual_no_path_joins_distinct_finite_grid_points G hG x y
      (by simpa only [Set.mem_singleton_iff,ne_eq,eq_comm] using h) hy
  · rintro rfl
    exact mem_pathComponentIn_self hx

/-- The same grid admits different discrete adjacency choices although its Euclidean paths
stay constant. Here vertices 0 and 1 have an edge, or have no edges. -/
theorem actual_graph_adjacency_and_euclidean_paths_differ :
    Relation.ReflTransGen (fun x y : ℝ=>x∈({0,1} : Set ℝ) ∧ y∈({0,1} : Set ℝ) ∧ x≠y) 0 1 ∧
    ¬Relation.ReflTransGen (fun _ _ : ℝ=>False) 0 1 ∧
    ¬JoinedIn ({0,1} : Set ℝ) 0 1 := by
  refine ⟨Relation.ReflTransGen.single (by norm_num),?_,?_⟩
  · rw [Relation.reflTransGen_iff_eq (by simp)]
    norm_num
  · exact actual_no_path_joins_distinct_finite_grid_points _ (by simp) _ _ (by norm_num)

/-- The actual single-witness lower-bound test is sound from a genuine Lipschitz estimate.
The truth of safety alone is not supplied as the premise of a certification theorem. -/
theorem actual_lipschitz_witness_certifies_true_safety {X : Type*} [PseudoMetricSpace X]
    (g : X→ℝ) (L : NNReal) (hg : LipschitzWith L g) (x y : X)
    (lower ε h : ℝ) (hlower : lower≤g x) (hε : 0≤ε)
    (hcert : h≤lower-ε-(L : ℝ)*dist x y) : h≤g y := by
  have hdist:=hg.dist_le_mul x y
  rw [Real.dist_eq] at hdist
  have hdiff: g x-g y≤(L : ℝ)*dist x y := (le_abs_self _).trans hdist
  linarith

/-- All points are truly safe and graph-adjacent, while the specified conservative margin
fails to certify the second point. This is the finite-grid distinction in the linked contexts. -/
theorem actual_safe_graph_neighbor_need_not_pass_lipschitz_certificate :
    LipschitzWith (1 : NNReal) (fun _ : ℝ=>(1 : ℝ)) ∧
    (1 : ℝ)≥1/2 ∧ dist (0 : ℝ) 1≤1 ∧
    ¬((1 : ℝ)-1/10-1*dist (0 : ℝ) 1≥1/2) := by
  refine ⟨?_,by norm_num,by norm_num,by norm_num⟩
  exact (LipschitzWith.const (1 : ℝ)).weaken (by norm_num)


/-- The displayed certified relation on a fixed finite grid also changes reachability,
independently of the Euclidean or chosen graph connectedness. -/
def twoPointCertificate (x y : ℝ) : Prop :=
  x∈({0,1} : Set ℝ) ∧ y∈({0,1} : Set ℝ) ∧ (1 : ℝ)-1/10-dist x y≥1/2

theorem actual_certificate_on_the_same_grid_cannot_reach_safe_neighbor :
    ¬Relation.ReflTransGen twoPointCertificate 0 1 := by
  intro h
  have hzero : ∀y : ℝ,Relation.ReflTransGen twoPointCertificate 0 y→y=0 := by
    intro y hy
    induction hy with
    | refl => rfl
    | @tail z y hz hzy ih =>
      rcases hzy with ⟨hzG,hyG,hcert⟩
      rw [ih] at hcert
      rcases Set.mem_insert_iff.mp hyG with rfl|hyone
      · rfl
      · have h1 : y=1 := Set.mem_singleton_iff.mp hyone
        rw [h1] at hcert
        norm_num at hcert
  have hbad:=hzero 1 h
  norm_num at hbad

end SafeLearning.CompleteFoundationsConnectednessWhole30


namespace SafeLearning.CompleteFoundationsConnectednessWhole30
open Set Topology

theorem actual_literal_pairwise_continuous_images_including_empty
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (A : Set X)
    (hA : sourcePairwisePathConnected A) (f : X→Y) (hf : ContinuousOn f A) :
    sourcePairwisePathConnected (f '' A) := by
  by_cases hne : A.Nonempty
  · have hmath:= (actual_nonempty_path_connected_definition A).mpr ⟨hne,hA⟩
    exact (actual_nonempty_path_connected_definition (f '' A)).mp (hmath.image' hf) |>.2
  · have he : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst A
    simp [sourcePairwisePathConnected]

theorem actual_literal_maximal_pairwise_subsets_empty_or_components
    {X : Type*} [TopologicalSpace X] (A B : Set X)
    (hB : sourcePairwisePathConnected B) (hBA : B⊆A)
    (hmax : ∀ C : Set X,B⊆C→C⊆A→sourcePairwisePathConnected C→C=B) :
    (A=∅ ∧ B=∅) ∨ ∃x∈B,B=pathComponentIn A x := by
  by_cases hne : B.Nonempty
  · right
    have hmath:= (actual_nonempty_path_connected_definition B).mpr ⟨hne,hB⟩
    apply actual_every_maximal_path_connected_subset_is_a_component A B hmath hBA
    intro C hBC hCA hC
    exact hmax C hBC hCA ((actual_nonempty_path_connected_definition C).mp hC).2
  · have hBe : B=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    left
    refine ⟨?_,hBe⟩
    by_contra hAe
    obtain ⟨x,hx⟩:= Set.nonempty_iff_ne_empty.mpr hAe
    have hsingle : sourcePairwisePathConnected ({x} : Set X) :=
      ((actual_nonempty_path_connected_definition _).mp (isPathConnected_singleton x)).2
    have heq := hmax {x} (by rw [hBe]; exact empty_subset _)
      (by intro y hy; simpa only [Set.mem_singleton_iff.mp hy] using hx) hsingle
    have hbad : x∈(∅ : Set X) := by rw [←hBe,←heq];simp
    simpa using hbad

theorem actual_open_euclidean_pairwise_convention_empty_or_connected
    {I : Type*} [Fintype I] (A : Set (I→ℝ)) (hA : IsOpen A) :
    sourcePairwisePathConnected A ↔ A=∅ ∨ IsConnected A := by
  constructor
  · intro h
    by_cases hne : A.Nonempty
    · right
      exact ((actual_nonempty_path_connected_definition A).mpr ⟨hne,h⟩).isConnected
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)
  · rintro (he|hc)
    · subst A;simp [sourcePairwisePathConnected]
    · exact ((actual_nonempty_path_connected_definition A).mp
        (hA.isConnected_iff_isPathConnected.mp hc)).2

end SafeLearning.CompleteFoundationsConnectednessWhole30
