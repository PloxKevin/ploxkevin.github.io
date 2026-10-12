import SafeLearning.CompleteMonitoringDeterministicPath23
import SafeLearning.CompleteMonitoringFaceClassification23
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory ProbabilityTheory
namespace SafeLearning.CompleteCoreMonitoringFixedSelector29
open SafeLearning.CompleteFiniteCMDPOccupancy
open SafeLearning.CompleteFiniteControlledPathMeasure
open SafeLearning.CompleteFiniteControlledPathMeasureLaws
open SafeLearning.CompleteFiniteControlledPathFlow
open SafeLearning.CompleteFiniteMarkovPathCorrespondence
open SafeLearning.CompleteMonitoringGeometry21
open SafeLearning.CompleteMonitoringFaces22
open SafeLearning.CompleteMonitoringMeans22
local instance : MeasurableSpace (Fin 3) := ⊤
local instance : MeasurableSingletonClass (Fin 3) := ⟨fun _ => MeasurableSet.of_discrete⟩

def action (l1 l2 : ℝ) (s : Fin 3) : Bool :=
  if s=0 then decide (l1<l2)
  else if s=1 then decide (1<l1 ∧ l2≤l1)
  else decide (1<l2 ∧ l1≤l2)

def advance (l1 l2 : ℝ) (s : Fin 3) : Fin 3 :=
  if s=0 then (if action l1 l2 s then 2 else 1)
  else (if action l1 l2 s then s else 0)

def orbit (l1 l2 : ℝ) (initial : Fin 3) : ℕ → Fin 3
  | 0 => initial
  | n+1 => advance l1 l2 (orbit l1 l2 initial n)

def initialModel (initial : Fin 3) : Model (Fin 3) Bool where
  initial s := if s=initial then 1 else 0
  initial_nonneg s := by split_ifs <;> norm_num
  initial_sum := by simp
  transition := model.transition
  transition_nonneg := model.transition_nonneg
  transition_sum := model.transition_sum

def stationaryPolicy (l1 l2 : ℝ) : Policy (Fin 3) Bool where
  action _ s a := if a=action l1 l2 s then 1 else 0
  action_nonneg _ _ _ := by split_ifs <;> norm_num
  action_sum _ s := by cases h : action l1 l2 s <;> simp [Fintype.sum_bool,h]

def law (l1 l2 : ℝ) (initial : Fin 3) : Measure (ℕ → Fin 3 × Bool) :=
  controlledPathMeasure (initialModel initial) (markovHistoryPolicy (stationaryPolicy l1 l2))

instance (l1 l2 : ℝ) (initial : Fin 3) : IsProbabilityMeasure (law l1 l2 initial) := by
  unfold law; infer_instance

theorem actual_selected_transition_has_mass_one (l1 l2 : ℝ) (s : Fin 3) :
    model.transition s (action l1 l2 s) (advance l1 l2 s)=1 := by
  simp [model,advance]

theorem actual_stationary_selector_has_dirac_state_marginals
    (l1 l2 : ℝ) (initial : Fin 3) (n : ℕ) (s : Fin 3) :
    stateMass (initialModel initial) (stationaryPolicy l1 l2) n s=
      if s=orbit l1 l2 initial n then 1 else 0 := by
  have ht (n : ℕ) (s : Fin 3) :
      (initialModel initial).transition (orbit l1 l2 initial n)
        (action l1 l2 (orbit l1 l2 initial n)) s=
      if s=orbit l1 l2 initial (n+1) then 1 else 0 := by
    rfl
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [stateMass]
    simp_rw [ih]
    simp [stationaryPolicy,ite_mul,mul_ite,ht]

theorem actual_genuine_stationary_controlled_law_follows_the_selected_orbit
    (l1 l2 : ℝ) (initial : Fin 3) :
    ∀ᵐ sample ∂law l1 l2 initial, ∀ n, (sample n).1=orbit l1 l2 initial n := by
  apply ae_all_iff.mpr; intro n
  have hm (a : Bool) := actual_constructed_markov_path_joint_mass
    (initialModel initial) (stationaryPolicy l1 l2) n (orbit l1 l2 initial n) a
  have hp := actual_finite_event_partition (law l1 l2 initial)
    (fun sample => (sample n).2) {sample | (sample n).1=orbit l1 l2 initial n}
    (fun a => by
      have hma : MeasurableSet {sample : ℕ → Fin 3 × Bool | (sample n).2=a} :=
        (measurableSet_singleton a).preimage (measurable_pi_apply n).snd
      have hms : MeasurableSet {sample : ℕ → Fin 3 × Bool | (sample n).1=orbit l1 l2 initial n} :=
        (measurableSet_singleton (orbit l1 l2 initial n)).preimage (measurable_pi_apply n).fst
      exact hma.inter hms)
  have he : (law l1 l2 initial).real {sample | (sample n).1=orbit l1 l2 initial n}=1 := by
    rw [hp]; simp only [Fintype.sum_bool]
    have hj (a : Bool) : (law l1 l2 initial).real
        {sample | (sample n).2=a ∧ sample ∈ {sample | (sample n).1=orbit l1 l2 initial n}}=
        (stationaryPolicy l1 l2).action n (orbit l1 l2 initial n) a := by
      have h := hm a
      rw [jointMass,actual_stationary_selector_has_dirac_state_marginals l1 l2 initial n (orbit l1 l2 initial n)] at h
      simpa [law,Prod.ext_iff,and_comm] using h
    simp_rw [hj]
    simpa [Fintype.sum_bool] using (stationaryPolicy l1 l2).action_sum n (orbit l1 l2 initial n)
  apply (ae_iff_prob_eq_one (by fun_prop)).mpr
  calc _ = ENNReal.ofReal ((law l1 l2 initial).real {sample | (sample n).1=orbit l1 l2 initial n}) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = 1 := by rw [he]; norm_num

theorem actual_two_transient_steps_reach_a_period_two_or_one_orbit
    (l1 l2 : ℝ) (s : Fin 3) :
    advance l1 l2 (advance l1 l2 (advance l1 l2 (advance l1 l2 s)))=
      advance l1 l2 (advance l1 l2 s) := by
  by_cases h12 : l1<l2 <;> by_cases h21 : l1≤l2 <;> by_cases h1 : 1<l1 <;> by_cases h2 : 1<l2
  all_goals have hle : (l2≤l1) ↔ ¬l1<l2 := not_lt.symm
  all_goals first | (exfalso; linarith) | (fin_cases s <;> simp [advance,action,h12,h21,h1,h2,hle])

theorem actual_fixed_selector_orbit_periodicity (l1 l2 : ℝ) (s : Fin 3) (n : ℕ) :
    orbit l1 l2 s (n+4)=orbit l1 l2 s (n+2) := by
  induction n with
  | zero => exact actual_two_transient_steps_reach_a_period_two_or_one_orbit l1 l2 s
  | succ n ih => simpa [orbit,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrArg (advance l1 l2) ih

def tailIndicator (l1 l2 : ℝ) (s target : Fin 3) (n : ℕ) : ℝ :=
  if orbit l1 l2 s (n+2)=target then 1 else 0

def fraction (l1 l2 : ℝ) (s target : Fin 3) : ℝ :=
  (tailIndicator l1 l2 s target 0+tailIndicator l1 l2 s target 1)/2

theorem actual_consecutive_tail_indicators_have_constant_sum
    (l1 l2 : ℝ) (s target : Fin 3) (n : ℕ) :
    tailIndicator l1 l2 s target n+tailIndicator l1 l2 s target (n+1)=
      2*fraction l1 l2 s target := by
  induction n with
  | zero => dsimp [fraction]; ring
  | succ n ih =>
    have hp : tailIndicator l1 l2 s target (n+2)=tailIndicator l1 l2 s target n := by
      simp only [tailIndicator,show n+2+2=n+4 by omega,actual_fixed_selector_orbit_periodicity]
    rw [show n+1+1=n+2 by omega,hp]
    linarith

def potential (l1 l2 : ℝ) (s target : Fin 3) (n : ℕ) : ℝ :=
  (fraction l1 l2 s target-tailIndicator l1 l2 s target n)/2

theorem actual_tail_indicator_telescope (l1 l2 : ℝ) (s target : Fin 3) (N : ℕ) :
    (∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n)=
      (N:ℝ)*fraction l1 l2 s target+potential l1 l2 s target N-potential l1 l2 s target 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    have hp := actual_consecutive_tail_indicators_have_constant_sum l1 l2 s target N
    dsimp [potential]
    push_cast
    linarith

theorem actual_tail_fraction_error_at_most_inverse_horizon
    (l1 l2 : ℝ) (s target : Fin 3) (N : ℕ) (hN : N≠0) :
    |(∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n)/(N:ℝ)-fraction l1 l2 s target|≤1/(N:ℝ) := by
  have hn : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have ht := actual_tail_indicator_telescope l1 l2 s target N
  have hb (n : ℕ) : 0≤tailIndicator l1 l2 s target n ∧ tailIndicator l1 l2 s target n≤1 := by
    dsimp [tailIndicator]; split_ifs <;> norm_num
  have hb0 := hb 0; have hbN := hb N
  have hmul : ((∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n)/(N:ℝ))*(N:ℝ)=
      ∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n := div_mul_cancel₀ _ (ne_of_gt hn)
  dsimp [potential] at ht
  apply abs_le.mpr; constructor
  · rw [←neg_div]; apply (div_le_iff₀ hn).mpr; nlinarith
  · apply (le_div_iff₀ hn).mpr; nlinarith

theorem actual_tail_fraction_limit (l1 l2 : ℝ) (s target : Fin 3) :
    Tendsto (fun N => (∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n)/(N:ℝ)) atTop
      (𝓝 (fraction l1 l2 s target)) := by
  have he : Tendsto (fun N => |(∑ n ∈ Finset.range N,tailIndicator l1 l2 s target n)/(N:ℝ)-fraction l1 l2 s target|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      ((eventually_ne_atTop (0:ℕ)).mono fun N h => actual_tail_fraction_error_at_most_inverse_horizon l1 l2 s target N h)
      (by simpa [one_div] using tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa [Real.dist_eq] using he)


def indicator (l1 l2 : ℝ) (s target : Fin 3) (n : ℕ) : ℝ :=
  if orbit l1 l2 s n=target then 1 else 0

def fullFraction (l1 l2 : ℝ) (s target : Fin 3) (T : ℕ) : ℝ :=
  (∑ n ∈ Finset.range T,indicator l1 l2 s target n)/(T:ℝ)

theorem actual_all_horizon_fraction_error_bound
    (l1 l2 : ℝ) (s target : Fin 3) (T : ℕ) (hT : 2≤T) :
    |fullFraction l1 l2 s target T-fraction l1 l2 s target|≤3/(T:ℝ) := by
  have hn : (0:ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hi (n : ℕ) : 0≤indicator l1 l2 s target n ∧ indicator l1 l2 s target n≤1 := by
    dsimp [indicator]; split_ifs <;> norm_num
  have htail (n : ℕ) : 0≤tailIndicator l1 l2 s target n ∧ tailIndicator l1 l2 s target n≤1 := by
    dsimp [tailIndicator]; split_ifs <;> norm_num
  have hi0 := hi 0; have hi1 := hi 1
  have ht0 := htail 0; have ht1 := htail 1; have htN := htail (T-2)
  have hf : 0≤fraction l1 l2 s target ∧ fraction l1 l2 s target≤1 := by
    dsimp [fraction]; constructor <;> linarith
  have hc : (∑ n ∈ Finset.range T,indicator l1 l2 s target n)=
      indicator l1 l2 s target 0+indicator l1 l2 s target 1+
      ((T:ℝ)-2)*fraction l1 l2 s target+
      potential l1 l2 s target (T-2)-potential l1 l2 s target 0 := by
    calc
      _ = (∑ n ∈ Finset.range 2,indicator l1 l2 s target n)+
          ∑ n ∈ Finset.range (T-2),tailIndicator l1 l2 s target n := by
        conv_lhs => rw [show T=2+(T-2) by omega,Finset.sum_range_add]
        congr 1; apply Finset.sum_congr rfl; intro n _
        simp [indicator,tailIndicator,Nat.add_comm]
      _ = _ := by
        rw [actual_tail_indicator_telescope]
        have castsub : ((T-2:ℕ):ℝ)=(T:ℝ)-2 := by rw [Nat.cast_sub hT]; norm_num
        rw [castsub]; norm_num [Finset.sum_range_succ]; ring
  have hm : fullFraction l1 l2 s target T*(T:ℝ)=
      ∑ n ∈ Finset.range T,indicator l1 l2 s target n := div_mul_cancel₀ _ (ne_of_gt hn)
  dsimp [potential] at hc
  apply abs_le.mpr; constructor
  · rw [←neg_div]; apply (div_le_iff₀ hn).mpr; nlinarith
  · apply (le_div_iff₀ hn).mpr; nlinarith

theorem actual_all_horizon_fixed_selector_fraction_limits
    (l1 l2 : ℝ) (s target : Fin 3) :
    Tendsto (fun T => fullFraction l1 l2 s target T) atTop (𝓝 (fraction l1 l2 s target)) := by
  have hb : Tendsto (fun T : ℕ => 3/(T:ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=(3:ℝ))).mul (tendsto_inv_atTop_nhds_zero_nat (𝕜:=ℝ))
  have he : Tendsto (fun T => |fullFraction l1 l2 s target T-fraction l1 l2 s target|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      ((eventually_ge_atTop (2:ℕ)).mono fun T h => actual_all_horizon_fraction_error_bound l1 l2 s target T h) hb
  exact (tendsto_iff_dist_tendsto_zero).mpr (by simpa [Real.dist_eq] using he)

theorem actual_genuine_fixed_selector_law_has_almost_sure_all_horizon_fraction_limits
    (l1 l2 : ℝ) (initial : Fin 3) :
    ∀ᵐ sample ∂law l1 l2 initial, ∀ target : Fin 3,
      Tendsto (fun T : ℕ => (∑ n ∈ Finset.range T,if (sample n).1=target then (1:ℝ) else 0)/(T:ℝ))
        atTop (𝓝 (fraction l1 l2 initial target)) := by
  filter_upwards [actual_genuine_stationary_controlled_law_follows_the_selected_orbit l1 l2 initial] with sample hs
  intro target
  simpa only [hs,fullFraction,indicator] using actual_all_horizon_fixed_selector_fraction_limits l1 l2 initial target

def limitingFractions (l1 l2 : ℝ) (s : Fin 3) : Fractions :=
  ⟨fraction l1 l2 s 0,fraction l1 l2 s 1,fraction l1 l2 s 2⟩

theorem actual_fixed_selector_limits_are_in_the_achievable_polytope
    (l1 l2 : ℝ) (s : Fin 3) : AchievablePolytope (limitingFractions l1 l2 s) := by
  by_cases h12 : l1<l2 <;> by_cases h21 : l1≤l2 <;> by_cases h1 : 1<l1 <;> by_cases h2 : 1<l2
  all_goals have hle : (l2≤l1) ↔ ¬l1<l2 := not_lt.symm
  all_goals first | (exfalso; linarith) | (fin_cases s <;> norm_num [AchievablePolytope,limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,h21,h1,h2,hle])

theorem actual_fixed_selector_is_a_lagrangian_maximizer_for_every_price_and_initial_state
    (l1 l2 : ℝ) (s : Fin 3) : IsMaximizer l1 l2 (limitingFractions l1 l2 s) := by
  refine ⟨actual_fixed_selector_limits_are_in_the_achievable_polytope l1 l2 s,?_⟩
  intro w hw
  have firstAbove (h12 : l2≤l1) (h1 : 1≤l1) : lagrangian l1 l2 w≤lagrangian l1 l2 vertex1 := by
    obtain ⟨h0,h1w,h2w,hs,hh⟩ := hw
    have a := mul_nonneg (sub_nonneg.mpr h12) h2w
    have b := mul_nonneg (sub_nonneg.mpr h1) h0
    dsimp [lagrangian,vertex1]
    nlinarith [congrArg (fun x : ℝ => l1*x) hs]
  have firstBelow (h12 : l2≤l1) (h1 : l1≤1) : lagrangian l1 l2 w≤lagrangian l1 l2 vertex3 := by
    obtain ⟨h0,h1w,h2w,hs,hh⟩ := hw
    have a := mul_nonneg (sub_nonneg.mpr h12) h2w
    have b := mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr hh)
    dsimp [lagrangian,vertex3]
    nlinarith [congrArg (fun x : ℝ => l1*x) hs]
  have secondAbove (h12 : l1≤l2) (h2 : 1≤l2) : lagrangian l1 l2 w≤lagrangian l1 l2 vertex2 := by
    obtain ⟨h0,h1w,h2w,hs,hh⟩ := hw
    have a := mul_nonneg (sub_nonneg.mpr h12) h1w
    have b := mul_nonneg (sub_nonneg.mpr h2) h0
    dsimp [lagrangian,vertex2]
    nlinarith [congrArg (fun x : ℝ => l2*x) hs]
  have secondBelow (h12 : l1≤l2) (h2 : l2≤1) : lagrangian l1 l2 w≤lagrangian l1 l2 vertex4 := by
    obtain ⟨h0,h1w,h2w,hs,hh⟩ := hw
    have a := mul_nonneg (sub_nonneg.mpr h12) h1w
    have b := mul_nonneg (sub_nonneg.mpr h2) (sub_nonneg.mpr hh)
    dsimp [lagrangian,vertex4]
    nlinarith [congrArg (fun x : ℝ => l2*x) hs]
  by_cases h12 : l1<l2
  · have hle : l1≤l2 := h12.le
    have hnle : ¬l2≤l1 := not_le.mpr h12
    by_cases h2 : 1<l2
    · have hb := secondAbove hle h2.le
      fin_cases s <;> simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,hnle,h2,lagrangian,vertex2] using hb
    · have h2le : l2≤1 := le_of_not_gt h2
      have h1 : ¬1<l1 := by linarith
      have hb := secondBelow hle h2le
      fin_cases s <;> simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,hnle,h2,h1,lagrangian,vertex4] using hb
  · have hle : l2≤l1 := le_of_not_gt h12
    by_cases h1 : 1<l1
    · have hb := firstAbove hle h1.le
      fin_cases s
      · simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,h1,lagrangian,vertex1] using hb
      · simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,h1,lagrangian,vertex1] using hb
      · by_cases hstay : 1<l2 ∧ l1≤l2
        · have heq : l1=l2 := le_antisymm hstay.2 hle
          simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,h1,hstay,heq,lagrangian,vertex1] using hb
        · simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,h1,hstay,lagrangian,vertex1] using hb
    · have h1le : l1≤1 := le_of_not_gt h1
      have h2 : ¬1<l2 := by linarith
      have hb := firstBelow hle h1le
      fin_cases s <;> simpa [limitingFractions,fraction,tailIndicator,orbit,advance,action,h12,hle,h1,h2,lagrangian,vertex3] using hb

end SafeLearning.CompleteCoreMonitoringFixedSelector29
