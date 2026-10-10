import SafeLearning.CompleteAppliedPendulumStability

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedPendulumSourceField
open SafeLearning.CompleteAppliedPendulumLinear
open SafeLearning.CompleteAppliedPendulumLocalField
open SafeLearning.CompleteAppliedGlobalLipschitzTrajectory

def familyField (b:ℝ) (x:ℝ×ℝ) : ℝ×ℝ := (x.2,b*Real.sin x.1-x.2/10)

theorem actual_source_pendulum_family_is_globally_lipschitz (b:ℝ) (hb:|b|≤10) :
    LipschitzWith (101/10) (familyField b) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hq : |x.1-y.1|≤‖x-y‖:=by simpa only [Real.norm_eq_abs,Prod.fst_sub] using norm_fst_le (x-y)
  have hv : |x.2-y.2|≤‖x-y‖:=by simpa only [Real.norm_eq_abs,Prod.snd_sub] using norm_snd_le (x-y)
  have hs:=Real.abs_sin_sub_sin_le x.1 y.1
  have ha : |(familyField b x).2-(familyField b y).2|≤(101/10:ℝ)*‖x-y‖ := by
    calc
      _=|b*(Real.sin x.1-Real.sin y.1)-(x.2-y.2)/10|:=by unfold familyField;congr 1;ring
      _≤|b| *|Real.sin x.1-Real.sin y.1|+|x.2-y.2|/10:=by
        simpa [abs_mul,abs_div] using abs_sub (b*(Real.sin x.1-Real.sin y.1)) ((x.2-y.2)/10)
      _≤10*|x.1-y.1|+|x.2-y.2|/10:=by gcongr
      _≤(101/10:ℝ)*‖x-y‖:=by linarith
  rw [dist_eq_norm,Prod.norm_def]
  change max |(familyField b x).1-(familyField b y).1|
    |(familyField b x).2-(familyField b y).2|≤(101/10:ℝ)*‖x-y‖
  apply max_le
  · change |x.2-y.2|≤_
    nlinarith [norm_nonneg (x-y)]
  · exact ha

theorem actual_both_source_pendulum_coordinate_fields_are_globally_lipschitz :
    LipschitzWith (101/10) field ∧ LipschitzWith (101/10) hangingField := by
  exact ⟨actual_source_pendulum_family_is_globally_lipschitz 10 (by norm_num),
    actual_source_pendulum_family_is_globally_lipschitz (-10) (by norm_num)⟩

def sourcePath (initial:ℝ×ℝ) : ℝ→ℝ×ℝ :=
  globalSolution field initial (101/10)
    actual_both_source_pendulum_coordinate_fields_are_globally_lipschitz.1
def physicalEnergy (x:ℝ×ℝ) : ℝ := 10*Real.cos x.1+x.2^2/2

theorem actual_source_pendulum_has_a_derived_global_trajectory (initial:ℝ×ℝ) :
    sourcePath initial 0=initial ∧ ContDiff ℝ 1 (sourcePath initial) ∧
      (∀ a b:ℝ,AbsolutelyContinuousOnInterval (sourcePath initial) a b) ∧
      ∀t:ℝ,HasDerivAt (sourcePath initial) (field (sourcePath initial t)) t := by
  exact ⟨actual_global_solution_initial_condition _ _ _ _,
    (actual_global_solution_is_c1_and_locally_absolutely_continuous _ _ _ _).1,
    (actual_global_solution_is_c1_and_locally_absolutely_continuous _ _ _ _).2,
    actual_global_solution_has_the_true_ode_at_every_real_time _ _ _ _⟩

theorem actual_source_physical_energy_has_its_true_damping_derivative (initial:ℝ×ℝ) (t:ℝ) :
    HasDerivAt (fun t=>physicalEnergy (sourcePath initial t))
      (-((sourcePath initial t).2)^2/10) t := by
  have hd:=(actual_source_pendulum_has_a_derived_global_trajectory initial).2.2.2 t
  have hq := (hasFDerivAt_fst : HasFDerivAt (@Prod.fst ℝ ℝ)
    (ContinuousLinearMap.fst ℝ ℝ ℝ) (sourcePath initial t)).comp_hasDerivAt t hd
  have hv := (hasFDerivAt_snd : HasFDerivAt (@Prod.snd ℝ ℝ)
    (ContinuousLinearMap.snd ℝ ℝ ℝ) (sourcePath initial t)).comp_hasDerivAt t hd
  have h:=(hq.cos.const_mul 10).add ((hv.pow 2).div_const 2)
  convert h using 1
  · funext s;dsimp [physicalEnergy]
  · dsimp [field];ring

theorem actual_source_physical_energy_never_increases (initial:ℝ×ℝ) (t:ℝ) (ht:0≤t) :
    physicalEnergy (sourcePath initial t)≤physicalEnergy initial := by
  have hc : ContDiff ℝ 1 (fun t=>physicalEnergy (sourcePath initial t)) := by
    have hp:=(actual_source_pendulum_has_a_derived_global_trajectory initial).2.1
    exact (contDiff_const.mul hp.fst.cos).add ((hp.snd.pow 2).div_const 2)
  have hd:=actual_source_physical_energy_has_its_true_damping_derivative initial
  have ha : Antitone (fun t=>physicalEnergy (sourcePath initial t)) := by
    apply antitone_of_deriv_nonpos (fun s=>(hd s).differentiableAt)
    intro s
    rw [(hd s).deriv]
    nlinarith [sq_nonneg ((sourcePath initial s).2)]
  have h:=ha ht
  change physicalEnergy (sourcePath initial t)≤physicalEnergy (sourcePath initial 0) at h
  rw [(actual_source_pendulum_has_a_derived_global_trajectory initial).1] at h
  exact h

end SafeLearning.CompleteAppliedPendulumSourceField
