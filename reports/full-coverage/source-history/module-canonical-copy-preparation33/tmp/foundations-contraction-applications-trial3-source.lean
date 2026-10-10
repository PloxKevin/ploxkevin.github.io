import SafeLearning.CompleteAppliedBellman
import SafeLearning.CompleteFoundationsBanachModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators NNReal
namespace SafeLearning.CompleteFoundationsContractionApplications

section SafetyBellman
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

def successorMaximum (next : S → A → S) (value : S → ℝ) (s : S) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (fun a => value (next s a))

def safetyBackup (next : S → A → S) (margin : S → ℝ) (gamma : ℝ)
    (value : S → ℝ) (s : S) : ℝ :=
  (1-gamma)*margin s+gamma*min (margin s) (successorMaximum next value s)

def feasibilityBackup (next : S → A → S) (violation : S → ℝ) (gamma : ℝ)
    (value : S → ℝ) (s : S) : ℝ :=
  (1-gamma)*violation s+gamma*max (violation s) (-successorMaximum next (fun t => -value t) s)

theorem actual_successor_maximum_does_not_enlarge_the_uniform_error
    (next : S → A → S) (value other : S → ℝ) (epsilon : ℝ)
    (he : ∀ s,|value s-other s|≤epsilon) (s : S) :
    |successorMaximum next value s-successorMaximum next other s|≤epsilon := by
  classical
  have upper (f g : S → ℝ) (h : ∀ s,f s≤g s+epsilon) :
      successorMaximum next f s ≤ successorMaximum next g s+epsilon := by
    unfold successorMaximum
    apply Finset.sup'_le
    intro a ha
    have hb := Finset.le_sup' (fun b => g (next s b)) (Finset.mem_univ a)
    linarith [h (next s a)]
  apply abs_le.mpr
  have hf := upper value other (fun s => by linarith [(abs_le.mp (he s)).2])
  have hg := upper other value (fun s => by linarith [(abs_le.mp (he s)).1])
  constructor <;> linarith

theorem actual_discounted_safety_backup_is_a_sup_norm_contraction
    (next : S → A → S) (margin : S → ℝ) (gamma : ℝ≥0) (hg : gamma<1) :
    ContractingWith gamma (safetyBackup next margin gamma) := by
  refine ⟨hg,LipschitzWith.of_dist_le_mul ?_⟩
  intro value other
  apply (dist_pi_le_iff (mul_nonneg gamma.coe_nonneg dist_nonneg)).mpr
  intro s
  have hm := actual_successor_maximum_does_not_enlarge_the_uniform_error next value other
    (dist value other) (fun t => by simpa only [Real.dist_eq] using dist_le_pi_dist value other t) s
  have hmin := abs_min_sub_min_le_max (margin s) (successorMaximum next value s)
    (margin s) (successorMaximum next other s)
  simp only [sub_self,abs_zero] at hmin
  rw [max_eq_right (abs_nonneg (successorMaximum next value s-
    successorMaximum next other s))] at hmin
  have hdiff : safetyBackup next margin gamma value s-safetyBackup next margin gamma other s=
      (gamma:ℝ)*(min (margin s) (successorMaximum next value s)-
        min (margin s) (successorMaximum next other s)) := by unfold safetyBackup;ring
  rw [Real.dist_eq,hdiff,abs_mul,abs_of_nonneg gamma.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (hmin.trans hm) gamma.coe_nonneg

omit [Fintype S] in
theorem actual_feasibility_backup_is_the_negative_safety_backup
    (next : S → A → S) (violation : S → ℝ) (gamma : ℝ) (value : S → ℝ) :
    feasibilityBackup next violation gamma value=
      fun s => -safetyBackup next (fun t => -violation t) gamma (fun t => -value t) s := by
  funext s
  unfold feasibilityBackup safetyBackup
  have hn : min (-violation s) (successorMaximum next (fun t => -value t) s)=
      -max (violation s) (-successorMaximum next (fun t => -value t) s) := by
    simpa only [neg_neg] using min_neg_neg (violation s)
      (-successorMaximum next (fun t => -value t) s)
  rw [hn]
  ring

theorem actual_discounted_feasibility_backup_is_a_sup_norm_contraction
    (next : S → A → S) (violation : S → ℝ) (gamma : ℝ≥0) (hg : gamma<1) :
    ContractingWith gamma (feasibilityBackup next violation gamma) := by
  refine ⟨hg,LipschitzWith.of_dist_le_mul ?_⟩
  intro value other
  have hs := (actual_discounted_safety_backup_is_a_sup_norm_contraction next
    (fun s => -violation s) gamma hg).2.dist_le_mul (fun s => -value s) (fun s => -other s)
  rw [actual_feasibility_backup_is_the_negative_safety_backup,
    actual_feasibility_backup_is_the_negative_safety_backup]
  simpa only [← Pi.neg_def,dist_neg_neg] using hs

theorem actual_safety_and_feasibility_backups_have_unique_fixed_points_and_true_iteration_limits
    (next : S → A → S) (margin : S → ℝ) (gamma : ℝ≥0) (hg : gamma<1)
    (initial : S → ℝ) :
    (∃ fixed : S → ℝ,safetyBackup next margin gamma fixed=fixed ∧
      Tendsto (fun n : ℕ => (safetyBackup next margin gamma)^[n] initial) atTop (𝓝 fixed) ∧
      ∀ other,safetyBackup next margin gamma other=other → other=fixed) ∧
    (∃ fixed : S → ℝ,feasibilityBackup next margin gamma fixed=fixed ∧
      Tendsto (fun n : ℕ => (feasibilityBackup next margin gamma)^[n] initial) atTop (𝓝 fixed) ∧
      ∀ other,feasibilityBackup next margin gamma other=other → other=fixed) := by
  constructor
  · have hc := actual_discounted_safety_backup_is_a_sup_norm_contraction next margin gamma hg
    obtain ⟨fixed,hf,ht,_⟩ := hc.exists_fixedPoint initial (edist_ne_top _ _)
    exact ⟨fixed,hf,ht,fun other ho => hc.fixedPoint_unique' ho hf⟩
  · have hc := actual_discounted_feasibility_backup_is_a_sup_norm_contraction next margin gamma hg
    obtain ⟨fixed,hf,ht,_⟩ := hc.exists_fixedPoint initial (edist_ne_top _ _)
    exact ⟨fixed,hf,ht,fun other ho => hc.fixedPoint_unique' ho hf⟩
end SafetyBellman

section Equilibrium
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def equilibriumMap (W : E →L[ℝ] E) (activation : E → E) (offset : E) (z : E) : E :=
  activation (W z+offset)

theorem actual_one_lipschitz_activation_and_linear_norm_make_the_equilibrium_map_lipschitz
    (W : E →L[ℝ] E) (activation : E → E) (offset : E)
    (hactivation : LipschitzWith 1 activation) :
    LipschitzWith ‖W‖₊ (equilibriumMap W activation offset) := by
  apply LipschitzWith.of_dist_le_mul
  intro z other
  calc
    dist (equilibriumMap W activation offset z) (equilibriumMap W activation offset other)
      ≤dist (W z+offset) (W other+offset) := by
        simpa only [equilibriumMap,NNReal.coe_one,one_mul] using
          hactivation.dist_le_mul (W z+offset) (W other+offset)
    _=‖W (z-other)‖ := by rw [dist_eq_norm];simp [map_sub]
    _≤‖W‖*‖z-other‖ := W.le_opNorm _
    _=(‖W‖₊:ℝ)*dist z other := by rw [dist_eq_norm];rfl

theorem actual_norm_below_one_proves_equilibrium_well_posedness_and_all_start_convergence
    [CompleteSpace E]
    (W : E →L[ℝ] E) (activation : E → E) (offset initial : E)
    (hactivation : LipschitzWith 1 activation) (hW : ‖W‖<1) :
    ∃ fixed : E,activation (W fixed+offset)=fixed ∧
      Tendsto (fun n : ℕ => (equilibriumMap W activation offset)^[n] initial) atTop (𝓝 fixed) ∧
      ∀ other,activation (W other+offset)=other → other=fixed := by
  have hc : ContractingWith ‖W‖₊ (equilibriumMap W activation offset) :=
    ⟨by exact_mod_cast hW,
      actual_one_lipschitz_activation_and_linear_norm_make_the_equilibrium_map_lipschitz
        W activation offset hactivation⟩
  obtain ⟨fixed,hf,ht,_⟩ := hc.exists_fixedPoint initial (edist_ne_top _ _)
  exact ⟨fixed,hf,ht,fun other ho => hc.fixedPoint_unique' ho hf⟩
end Equilibrium
end SafeLearning.CompleteFoundationsContractionApplications
