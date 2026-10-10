import SafeLearning.CompleteExponentialBarrier

set_option autoImplicit false
noncomputable section
open Set

namespace SafeLearning.CompleteExponentialBarrierSafety
open CompleteExponentialBarrier CompleteCoreControl

theorem actual_nested_barrier_forward_invariance (p v u : ℝ → ℝ)
    (p1 p2 horizon : ℝ) (hT : 0 ≤ horizon)
    (hpcont : ContinuousOn p (Icc 0 horizon))
    (hvcont : ContinuousOn v (Icc 0 horizon))
    (hp : ∀ t ∈ Ioo 0 horizon, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Ioo 0 horizon, HasDerivAt v (u t) t)
    (hconstraint : ∀ t ∈ Ioo 0 horizon,
      u t ≤ p1 * p2 * (1 - p t) - (p1 + p2) * v t)
    (hinit : 0 ≤ barrier (p 0)) (hauxinit : 0 ≤ auxiliary p1 (p 0) (v 0)) :
    ∀ t ∈ Icc 0 horizon, 0 ≤ auxiliary p1 (p t) (v t) ∧ p t ≤ 1 := by
  have hc : ContinuousOn (fun t => auxiliary p1 (p t) (v t)) (Icc 0 horizon) := by
    exact hvcont.neg.add ((continuousOn_const.sub hpcont).const_mul p1)
  have hd : ∀ t ∈ Ioo 0 horizon, HasDerivAt (fun s => auxiliary p1 (p s) (v s))
      (auxiliaryRate p1 (v t) (u t)) t := by
    intro t ht
    exact genuine_auxiliary_derivative p v p1 (u t) t (hp t ht) (hv t ht)
  have hb : ∀ t ∈ Ioo 0 horizon,
      -p2 * auxiliary p1 (p t) (v t) ≤ auxiliaryRate p1 (v t) (u t) := by
    intro t ht
    have h := hconstraint t ht
    unfold auxiliaryRate auxiliary barrier
    nlinarith
  have haux := barrier_invariance (fun t => auxiliary p1 (p t) (v t))
    (fun t => auxiliaryRate p1 (v t) (u t)) p2 horizon hT hc hd hb hauxinit
  have hbc : ContinuousOn (fun t => barrier (p t)) (Icc 0 horizon) := by
    exact continuousOn_const.sub hpcont
  have hbd : ∀ t ∈ Ioo 0 horizon, HasDerivAt (fun s => barrier (p s)) (-v t) t := by
    intro t ht
    exact (genuine_double_integrator_barrier_derivatives p v (u t) t (hp t ht) (hv t ht)).1
  have hbb : ∀ t ∈ Ioo 0 horizon, -p1 * barrier (p t) ≤ -v t := by
    intro t ht
    have h := haux t ⟨ht.1.le, ht.2.le⟩
    unfold auxiliary at h
    linarith
  have hsafe := barrier_invariance (fun t => barrier (p t)) (fun t => -v t)
    p1 horizon hT hbc hbd hbb hinit
  intro t ht
  refine ⟨haux t ht, ?_⟩
  have h := hsafe t ht
  unfold barrier at h
  linarith

theorem actual_source_choice_keeps_position_safe (p v u : ℝ → ℝ)
    (horizon : ℝ) (hT : 0 ≤ horizon)
    (hpcont : ContinuousOn p (Icc 0 horizon))
    (hvcont : ContinuousOn v (Icc 0 horizon))
    (hp : ∀ t ∈ Ioo 0 horizon, HasDerivAt p (v t) t)
    (hv : ∀ t ∈ Ioo 0 horizon, HasDerivAt v (u t) t)
    (hconstraint : ∀ t ∈ Ioo 0 horizon, u t ≤ 4 * (1 - p t) - 4 * v t)
    (hp0 : p 0 = 0) (hv0 : v 0 = 1) :
    ∀ t ∈ Icc 0 horizon, p t ≤ 1 := by
  have h := actual_nested_barrier_forward_invariance p v u 2 2 horizon hT
    hpcont hvcont hp hv (by intro t ht; norm_num; exact hconstraint t ht)
    (by norm_num [barrier, hp0]) (by norm_num [auxiliary, barrier, hp0, hv0])
  intro t ht
  exact (h t ht).2

theorem positive_linear_class_K (pole : ℝ) (hpole : 0 < pole) :
    (fun r : ℝ => pole * r) 0 = 0 ∧ StrictMono (fun r : ℝ => pole * r) := by
  refine ⟨by simp, ?_⟩
  intro x y hxy
  exact mul_lt_mul_of_pos_left hxy hpole

theorem literal_nested_linear_constraint (p1 p2 p v u : ℝ) :
    auxiliaryRate p1 v u + p2 * auxiliary p1 p v =
      -u + p1 * p2 * (1 - p) - (p1 + p2) * v := by
  unfold auxiliaryRate auxiliary barrier
  ring

end SafeLearning.CompleteExponentialBarrierSafety
