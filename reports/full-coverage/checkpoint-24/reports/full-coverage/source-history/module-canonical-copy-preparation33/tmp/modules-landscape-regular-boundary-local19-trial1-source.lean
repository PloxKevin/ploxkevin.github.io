import SafeLearning.CompleteModulesLandscapeRegularBoundaryPerturbation
import SafeLearning.CompleteModulesLandscapeLocalExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeRegularBoundaryLocal

open SafeLearning.CompleteModulesLandscapeRegularBoundaryPerturbation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Constant perturbations of a bounded Lipschitz field admit true Picard
solutions in the same certified ball and on one common positive time interval. -/
theorem actual_constant_perturbations_have_a_uniform_picard_interval
    (F : E → E) (x₀ v : E) (r L K : ℝ≥0) (hr : 0 < r)
    (hbound : ∀ z ∈ closedBall x₀ r, ‖F z‖ ≤ L)
    (hLip : LipschitzOnWith K F (closedBall x₀ r)) :
    ∃ η > (0 : ℝ), ∀ ε ∈ Ioo (0 : ℝ) 1, ∃ W : ℝ → E,
      W 0 = x₀ ∧ (∀ t, W t ∈ closedBall x₀ r) ∧
      ContinuousOn W (Icc 0 η) ∧
      ∀ t ∈ Ico 0 η, HasDerivAt W (F (W t) + ε • v) t := by
  let B : ℝ := L + ‖v‖ + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let η : ℝ := (r : ℝ) / B
  have hη : 0 < η := by dsimp [η]; exact div_pos (by exact_mod_cast hr) hB
  let BNN : ℝ≥0 := ⟨B,hB.le⟩
  let tinit : Icc (-η) η := ⟨0,by constructor <;> linarith⟩
  refine ⟨η,hη,?_⟩
  intro ε hε
  have hboundε : ∀ z ∈ closedBall x₀ r, ‖F z + ε • v‖ ≤ B := by
    intro z hz
    calc
      ‖F z + ε • v‖ ≤ ‖F z‖ + ε * ‖v‖ := by
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hε.1] using norm_add (F z) (ε • v)
      _ ≤ L + ‖v‖ := by
        gcongr
        · exact hbound z hz
        · exact hε.2.le
      _ ≤ B := by dsimp [B]; linarith
  have hLipε : LipschitzOnWith K (fun z => F z + ε • v) (closedBall x₀ r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro z hz w hw
    simpa only [dist_add_right] using hLip.dist_le_mul z hz w hw
  have hPL : IsPicardLindelof (fun _ z => F z + ε • v) tinit x₀ r 0 BNN K := by
    apply IsPicardLindelof.of_time_independent hboundε hLipε
    change B * max (η - 0) (0 - (-η)) ≤ (r : ℝ) - 0
    simp only [sub_zero,sub_neg_eq_add,zero_add,max_self]
    dsimp [η]
    rw [mul_div_cancel₀ _ (ne_of_gt hB)]
  obtain ⟨W,hinit,hball,hderiv⟩ :=
    SafeLearning.CompleteModulesLandscapeLocalExistence.actual_picard_solution_exists_and_stays_in_its_certified_ball
      (fun _ z => F z + ε • v) tinit x₀ r BNN K hPL
  have hsubset : Icc 0 η ⊆ Icc (-η) η := by
    intro t ht
    exact ⟨by linarith [ht.1],ht.2⟩
  refine ⟨W,hinit,hball,?_,?_⟩
  · intro t ht
    exact ((hderiv t (hsubset ht)).mono hsubset).continuousWithinAt
  · intro t ht
    exact (hderiv t (hsubset (Ico_subset_Icc_self ht))).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) ht.2)

/-- An existing true path starting at a regular zero of h has a genuinely safe
positive time prefix under the weak boundary-only inward condition. Uniform
Picard perturbations, strict fencing, and Gronwall derive the weak result. -/
theorem actual_regular_boundary_only_inward_condition_gives_local_safety_of_an_existing_path
    (F : E → E) (h : E → ℝ) (D : Set E) (hD : IsOpen D)
    (hf : LocallyLipschitzOn D F) (hh : ContDiffOn ℝ 1 h D)
    (x : ℝ → E) (T : ℝ) (hT : 0 < T)
    (hx : ContinuousOn x (Icc 0 T)) (hxD : MapsTo x (Icc 0 T) D)
    (hODE : ∀ t ∈ Ico 0 T, HasDerivWithinAt x (F (x t)) (Ici t) t)
    (hzero : h (x 0) = 0) (hregular : fderiv ℝ h (x 0) ≠ 0)
    (hinward : ∀ z ∈ D, h z = 0 → 0 ≤ fderiv ℝ h z (F z)) :
    ∃ γ > (0 : ℝ), γ < T ∧ ∀ t ∈ Icc 0 γ, 0 ≤ h (x t) := by
  classical
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl,hT.le⟩
  obtain ⟨v,r,hr,hrD,hdir,hstrict⟩ :=
    actual_regular_boundary_has_a_locally_strict_constant_inward_perturbation
      F h D hD hh (x 0) (hxD h0) hregular hinward
  obtain ⟨K,s,hs,hL⟩ := hf (hxD h0)
  have hs' : s ∈ 𝓝 (x 0) := by
    rwa [nhdsWithin_eq_nhds.mpr (hD.mem_nhds (hxD h0))] at hs
  obtain ⟨a,ha,has⟩ := Metric.mem_nhds_iff.mp (inter_mem hs' (ball_mem_nhds (x 0) hr))
  have hball : closedBall (x 0) (a / 2) ⊆ s ∩ ball (x 0) r :=
    (closedBall_subset_ball (half_lt_self ha)).trans has
  let R : ℝ≥0 := ⟨a / 2,(half_pos ha).le⟩
  let L : ℝ≥0 := ⟨K * a + ‖F (x 0)‖,by positivity⟩
  have hbound : ∀ z ∈ closedBall (x 0) R, ‖F z‖ ≤ L := by
    intro z hz
    calc
      ‖F z‖ ≤ ‖F z - F (x 0)‖ + ‖F (x 0)‖ := norm_le_norm_sub_add _ _
      _ ≤ K * ‖z - x 0‖ + ‖F (x 0)‖ := by
        gcongr
        exact hL.norm_sub_le (hball hz).1 (mem_of_mem_nhds hs')
      _ ≤ K * a + ‖F (x 0)‖ := by
        gcongr
        exact (mem_closedBall_iff_norm.mp hz).trans (half_le_self ha.le)
      _ = L := rfl
  have hLip : LipschitzOnWith K F (closedBall (x 0) R) :=
    hL.mono (fun z hz => (hball hz).1)
  obtain ⟨η,hη,hW⟩ := actual_constant_perturbations_have_a_uniform_picard_interval
    F (x 0) v R L K (by exact_mod_cast half_pos ha) hbound hLip
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousWithinAt_iff.mp (hx 0 h0) (a / 2) (half_pos ha)
  let γ : ℝ := min η (min δ T) / 2
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hγη : γ < η := by
    have hm : min η (min δ T) ≤ η := min_le_left _ _
    dsimp [γ]; linarith
  have hγδ : γ < δ := by
    have hm : min η (min δ T) ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
    dsimp [γ]; linarith
  have hγT : γ < T := by
    have hm : min η (min δ T) ≤ T := (min_le_right _ _).trans (min_le_right _ _)
    dsimp [γ]; linarith
  have htime : Icc 0 γ ⊆ Icc 0 T := Icc_subset_Icc_right hγT.le
  have htimeη : Icc 0 γ ⊆ Icc 0 η := Icc_subset_Icc_right hγη.le
  have hxball : ∀ t ∈ Icc 0 γ, x t ∈ closedBall (x 0) R := by
    intro t ht
    apply ball_subset_closedBall
    apply mem_ball.mpr
    apply hclose (htime ht)
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg ht.1] using ht.2.trans_lt hγδ
  have happrox : ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ t ∈ Icc 0 γ,
      ∃ z : E, 0 ≤ h z ∧ dist (x t) z ≤ gronwallBound 0 K (ε * ‖v‖) t := by
    intro ε hε t ht
    obtain ⟨W,hinit,hWC,hWcont,hWderiv⟩ := hW ε hε
    have hsafe : ∀ u ∈ Icc 0 γ, 0 ≤ h (W u) := by
      apply actual_strict_boundary_vector_ode_path_stays_in_the_superlevel_set
        (fun z => F z + ε • v) h (ball (x 0) r) isOpen_ball (hh.mono hrD)
        W 0 γ (hWcont.mono htimeη)
        (fun u _ => (hball (hWC u)).2)
        (fun u hu => (hWderiv u ⟨hu.1,hu.2.trans hγη⟩).hasDerivWithinAt)
        (by simp only [hinit,hzero,le_refl])
        (fun z hz hzeroz => hstrict ε hε.1 z hz hzeroz)
    have hdist : dist (x t) (W t) ≤ gronwallBound 0 K (ε * ‖v‖) t := by
      have hd := dist_le_of_approx_trajectories_ODE_of_mem
        (fun _ _ => hLip) (hx.mono htime)
        (fun u hu => hODE u ⟨hu.1,hu.2.trans hγT⟩)
        (fun _ _ => by simp) (fun u hu => hxball u (Ico_subset_Icc_self hu))
        (hWcont.mono htimeη)
        (fun u hu => (hWderiv u ⟨hu.1,hu.2.trans hγη⟩).hasDerivWithinAt)
        (fun u _ => by
          simp only [dist_eq_norm,add_sub_cancel_right,norm_smul,Real.norm_eq_abs,abs_of_pos hε.1,le_refl])
        (fun u _ => hWC u) (by simp only [hinit,dist_self,le_refl]) t ht
      simpa only [zero_add,sub_zero] using hd
    exact ⟨W t,hsafe t ht,hdist⟩
  refine ⟨γ,hγ,hγT,?_⟩
  intro t ht
  by_contra hn
  have hneg : h (x t) < 0 := lt_of_not_ge hn
  have hhxt : ContinuousAt h (x t) := hh.continuousOn.continuousAt (hD.mem_nhds (hxD (htime ht)))
  obtain ⟨ρ,hρ,hρball⟩ := Metric.mem_nhds_iff.mp (hhxt.preimage_mem_nhds (Iio_mem_nhds hneg))
  have hBcont : Continuous (fun ε : ℝ => gronwallBound 0 K (ε * ‖v‖) t) := by
    convert (gronwallBound_continuous_ε 0 K t).comp (continuous_id.mul_const ‖v‖) using 1
  have hsmall0 : {ε : ℝ | gronwallBound 0 K (ε * ‖v‖) t < ρ} ∈ 𝓝 (0 : ℝ) := by
    apply hBcont.continuousAt.preimage_mem_nhds
    simpa only [zero_mul,gronwallBound_ε0_δ0] using (Iio_mem_nhds hρ)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ε ∈ Ioo (0 : ℝ) 1 ∧ gronwallBound 0 K (ε * ‖v‖) t < ρ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)),
      mem_nhdsWithin_of_mem_nhds hsmall0] with ε hpos hone hsmallε
    exact ⟨⟨hpos,hone⟩,hsmallε⟩
  obtain ⟨ε,hε,hεsmall⟩ := hsmall.exists
  obtain ⟨z,hzsafe,hzdist⟩ := happrox ε hε t ht
  have hzball : z ∈ ball (x t) ρ := mem_ball.mpr (by rw [dist_comm]; exact hzdist.trans_lt hεsmall)
  exact (not_lt_of_ge hzsafe) (hρball hzball)

end SafeLearning.CompleteModulesLandscapeRegularBoundaryLocal
