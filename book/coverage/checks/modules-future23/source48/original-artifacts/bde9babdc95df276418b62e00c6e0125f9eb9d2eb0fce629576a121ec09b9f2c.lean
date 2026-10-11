import SafeLearning.CompleteModulesLipSDP

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Set Filter
open scoped Topology BigOperators
open SafeLearning.CompleteModulesLipSDP
namespace SafeLearning.CompleteModulesNNActivationPractices22

def shifted (base s : ℝ) : ℝ := max (s+base) 0-max base 0
def firstShift (s : ℝ) : ℝ := max (s+1) 0-1
def secondShift (s : ℝ) : ℝ := max (s-1) 0

theorem actual_literal_relu_shift_values_and_inequality :
    firstShift 0=0 ∧ secondShift 0=0 ∧ firstShift (1/2)=1/2 ∧
      secondShift (1/2)=0 ∧ firstShift ≠ secondShift := by
  refine ⟨by norm_num [firstShift],by norm_num [secondShift],
    by norm_num [firstShift],by norm_num [secondShift],?_⟩
  intro h
  have he := congrFun h (1/2)
  norm_num [firstShift,secondShift] at he

theorem actual_any_equilibrium_shift_preserves_individual_slope_and_sector
    (base : ℝ) :
    shifted base 0=0 ∧ slopeRestricted (shifted base) 0 1 ∧
      ∀ s : ℝ, 0 ≤ 2*(shifted base s)*(s-shifted base s) := by
  have hs : slopeRestricted (shifted base) 0 1 := by
    intro x y
    obtain ⟨d,hd0,hd1,he⟩ := relu_slope_restricted (x+base) (y+base)
    refine ⟨d,hd0,hd1,?_⟩
    dsimp [shifted]
    convert he using 1 <;> ring
  refine ⟨by simp [shifted],hs,?_⟩
  intro s
  have h := scalar_slope_quadratic_constraint (shifted base) 0 1 hs s 0
  simp only [shifted,zero_add,sub_self,sub_zero] at h
  convert h using 1 <;> ring

theorem actual_both_literal_channels_keep_their_individual_qcs :
    slopeRestricted firstShift 0 1 ∧ slopeRestricted secondShift 0 1 ∧
      (∀ s,0 ≤ 2*(firstShift s)*(s-firstShift s)) ∧
      (∀ s,0 ≤ 2*(secondShift s)*(s-secondShift s)) := by
  have h1 := actual_any_equilibrium_shift_preserves_individual_slope_and_sector 1
  have h2 := actual_any_equilibrium_shift_preserves_individual_slope_and_sector (-1)
  have e1 : shifted 1=firstShift := by funext s; norm_num [shifted,firstShift]
  have e2 : shifted (-1)=secondShift := by funext s; norm_num [shifted,secondShift]
  rw [e1] at h1
  rw [e2] at h2
  exact ⟨h1.2.1,h2.2.1,h1.2.2,h2.2.2⟩

def multiplier (d : ℝ) : ℝ := 6/5-d/2
def sectorStep (d x : ℝ) : ℝ := (6/5)*x-(1/2)*(d*x)
def sectorOrbit (d x : ℝ) (n : ℕ) : ℝ := (sectorStep d)^[n] x

theorem actual_scalar_family_step_and_all_iterates (d x : ℝ) (n : ℕ) :
    sectorStep d x=multiplier d*x ∧ sectorOrbit d x n=(multiplier d)^n*x := by
  have he (y : ℝ) : sectorStep d y=multiplier d*y := by dsimp [sectorStep,multiplier];ring
  refine ⟨he x,?_⟩
  induction n with
  | zero => simp [sectorOrbit]
  | succ n ih =>
    simp only [sectorOrbit,Function.iterate_succ_apply']
    rw [he,show ((sectorStep d)^[n]) x=(multiplier d)^n*x from ih]
    rw [pow_succ]
    ring

theorem actual_scalar_asymptotic_stability_iff_strict_multiplier (d : ℝ) :
    (∀ x : ℝ,Tendsto (sectorOrbit d x) atTop (𝓝 0)) ↔ |multiplier d|<1 := by
  constructor
  · intro h
    have h1 := h 1
    have he : sectorOrbit d 1=(fun n : ℕ => (multiplier d)^n) := by
      funext n
      simp only [(actual_scalar_family_step_and_all_iterates d 1 n).2,mul_one]
    rw [he] at h1
    exact tendsto_pow_atTop_nhds_zero_iff.mp h1
  · intro h x
    have ht := (tendsto_pow_atTop_nhds_zero_iff.mpr h).mul_const x
    convert ht using 1
    · funext n
      exact (actual_scalar_family_step_and_all_iterates d x n).2
    · simp

theorem actual_multiplier_range_and_monotonicity (alpha d : ℝ)
    (hd : d ∈ Icc alpha 1) :
    multiplier d ∈ Icc (7/10:ℝ) (multiplier alpha) ∧
      multiplier 1=7/10 ∧ (∀ first second : ℝ,first ≤ second → multiplier second ≤ multiplier first) := by
  refine ⟨?_,by norm_num [multiplier],?_⟩
  · constructor <;> dsimp [multiplier] <;> linarith [hd.1,hd.2]
  · intro first second h; dsimp [multiplier];linarith

theorem actual_every_sector_member_is_stable_iff_alpha_above_two_fifths
    (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    (∀ d ∈ Icc alpha 1,∀ x : ℝ,Tendsto (sectorOrbit d x) atTop (𝓝 0)) ↔
      2/5<alpha := by
  constructor
  · intro h
    have hm := actual_scalar_asymptotic_stability_iff_strict_multiplier alpha |>.mp
      (h alpha ⟨le_rfl,ha1⟩)
    have hnonneg : 0 ≤ multiplier alpha := by dsimp [multiplier];linarith
    rw [abs_of_nonneg hnonneg] at hm
    dsimp [multiplier] at hm
    linarith
  · intro halpha d hd
    apply actual_scalar_asymptotic_stability_iff_strict_multiplier d |>.mpr
    have hb := (actual_multiplier_range_and_monotonicity alpha d hd).1
    rw [abs_of_nonneg (by linarith [hb.1] : 0 ≤ multiplier d)]
    have hu : multiplier alpha < 1 := by dsimp [multiplier];linarith
    linarith [hb.2]

theorem actual_stable_sector_has_a_common_geometric_envelope_and_stability
    (alpha : ℝ) (ha : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hstrict : 2/5<alpha)
    (d : ℝ) (hd : d ∈ Icc alpha 1) (x : ℝ) (n : ℕ) :
    0 ≤ multiplier alpha ∧ multiplier alpha<1 ∧
      |sectorOrbit d x n| ≤ (multiplier alpha)^n*|x| ∧
      |sectorOrbit d x n| ≤ |x| := by
  have hb := (actual_multiplier_range_and_monotonicity alpha d hd).1
  have hq0 : 0 ≤ multiplier alpha := by dsimp [multiplier];linarith
  have hq1 : multiplier alpha<1 := by dsimp [multiplier];linarith
  have hd0 : 0 ≤ multiplier d := by linarith [hb.1]
  have he : |sectorOrbit d x n| ≤ (multiplier alpha)^n*|x| := by
    rw [(actual_scalar_family_step_and_all_iterates d x n).2,abs_mul,abs_pow,
      abs_of_nonneg hd0]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg x)
    gcongr
    exact hb.2
  refine ⟨hq0,hq1,he,?_⟩
  have hp : (multiplier alpha)^n ≤ 1 := pow_le_one₀ hq0 hq1.le
  exact he.trans (by nlinarith [abs_nonneg x])

theorem actual_source_zero_half_and_boundary_comparisons :
    multiplier 0=6/5 ∧ multiplier (1/2)=19/20 ∧ multiplier (2/5)=1 ∧
      (∀ n : ℕ,sectorOrbit (2/5) 1 n=1) ∧
      ¬(∀ x : ℝ,Tendsto (sectorOrbit 0 x) atTop (𝓝 0)) ∧
      (∀ d ∈ Icc (1/2:ℝ) 1,multiplier d ∈ Icc (7/10:ℝ) (19/20)) ∧
      (∀ d ∈ Icc (1/2:ℝ) 1,∀ x : ℝ,Tendsto (sectorOrbit d x) atTop (𝓝 0)) := by
  have e0 : multiplier 0=6/5 := by norm_num [multiplier]
  have eh : multiplier (1/2)=19/20 := by norm_num [multiplier]
  have eb : multiplier (2/5)=1 := by norm_num [multiplier]
  refine ⟨e0,eh,eb,?_,?_,?_,?_⟩
  · intro n
    rw [(actual_scalar_family_step_and_all_iterates (2/5) 1 n).2,eb]
    simp
  · rw [actual_scalar_asymptotic_stability_iff_strict_multiplier,e0]
    norm_num
  · intro d hd
    simpa only [eh] using (actual_multiplier_range_and_monotonicity (1/2) d hd).1
  · exact (actual_every_sector_member_is_stable_iff_alpha_above_two_fifths (1/2)
      (by norm_num) (by norm_num)).2 (by norm_num)

def previous (a : ℕ → ℝ) (t : ℕ) : ℝ := if t=0 then 0 else a (t-1)
def sample (a : ℕ → ℝ) (t : ℕ) : ℝ := a t*(a t-previous a t)

theorem actual_iqc_sample_square_identity (current old : ℝ) :
    2*current*(current-old)=current^2-old^2+(current-old)^2 := by ring

theorem actual_every_finite_horizon_has_the_literal_hard_iqc_identity
    (a : ℕ → ℝ) (N : ℕ) :
    (∑ t ∈ Finset.range (N+1),sample a t)=
      (1/2)*(a N)^2+(1/2)*∑ t ∈ Finset.range (N+1),(a t-previous a t)^2 := by
  induction N with
  | zero => simp [sample,previous];ring
  | succ N ih =>
    have hl := Finset.sum_range_succ (sample a) (N+1)
    have hr := Finset.sum_range_succ (fun t => (a t-previous a t)^2) (N+1)
    rw [hl,hr,ih]
    simp only [sample,previous,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,
      if_false,Nat.add_sub_cancel]
    ring

theorem actual_every_hard_iqc_prefix_is_nonnegative (a : ℕ → ℝ) (N : ℕ) :
    0 ≤ ∑ t ∈ Finset.range (N+1),sample a t := by
  rw [actual_every_finite_horizon_has_the_literal_hard_iqc_identity]
  positivity

def literalV (t : ℕ) : ℝ := if t=0 then 2 else if t=1 then 1 else 0
def literalA (t : ℕ) : ℝ := literalV t/2

theorem actual_source_half_relation_and_negative_sample :
    literalA 0=1 ∧ literalA 1=1/2 ∧ sample literalA 0=1 ∧
      sample literalA 1= -1/4 ∧
      (∑ t ∈ Finset.range 1,sample literalA t)=1 ∧
      (∑ t ∈ Finset.range 2,sample literalA t)=3/4 ∧
      sample literalA 1<0 ∧ 0 ≤ ∑ t ∈ Finset.range 2,sample literalA t := by
  norm_num [literalA,literalV,sample,previous,Finset.sum_range_succ]

end SafeLearning.CompleteModulesNNActivationPractices22
