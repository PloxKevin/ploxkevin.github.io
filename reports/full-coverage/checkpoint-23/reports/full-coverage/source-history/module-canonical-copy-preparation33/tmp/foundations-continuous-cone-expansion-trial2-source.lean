import SafeLearning.CompleteFoundationsFiniteSetIteration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsContinuousConeExpansion
open CompleteFoundationsFiniteSetIteration

def safeDomain : Set ℝ := Icc 0 1
def safetyValue (x : ℝ) : ℝ := x/2
def coneExpansion (Y : Set ℝ) : Set ℝ :=
  Y∪{x | x∈safeDomain ∧ ∃y∈Y,safetyValue y-|x-y|≥0}
def seed : Set ℝ := {1}
def prefixes : ℕ→Set ℝ := iteration coneExpansion seed

theorem actual_safety_function_has_a_legitimate_global_one_lipschitz_bound
    (x y : ℝ) : |safetyValue x-safetyValue y|≤|x-y| := by
  have he : safetyValue x-safetyValue y=(x-y)/2 := by unfold safetyValue;ring
  rw [he,abs_div]
  norm_num

theorem actual_continuous_domain_cone_expansion_is_monotone : Monotone coneExpansion := by
  intro Y Z h x hx
  rcases hx with hx | ⟨hdom,y,hy,hcone⟩
  · exact Or.inl (h hx)
  · exact Or.inr ⟨hdom,y,h hy,hcone⟩

theorem actual_continuous_domain_cone_step_has_the_true_interval_formula
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    coneExpansion (Icc a 1)=Icc (a/2) 1 := by
  ext x
  constructor
  · rintro (hx | ⟨hdom,y,hy,hcone⟩)
    · exact ⟨by linarith [hx.1],hx.2⟩
    · have hb := neg_le_abs (x-y)
      unfold safetyValue at hcone
      exact ⟨by linarith [hy.1],hdom.2⟩
  · intro hx
    by_cases hxa : a≤x
    · exact Or.inl ⟨hxa,hx.2⟩
    · apply Or.inr
      refine ⟨⟨by linarith [hx.1],hx.2⟩,a,⟨le_rfl,ha1⟩,?_⟩
      have hn : x-a≤0 := by linarith
      rw [abs_of_nonpos hn]
      unfold safetyValue
      linarith [hx.1]

theorem actual_every_continuous_safeopt_prefix_is_the_true_closed_interval
    (n : ℕ) : prefixes n=Icc ((1/2:ℝ)^n) 1 := by
  induction n with
  | zero =>
    ext x
    simp [prefixes,iteration,seed]
  | succ n ih =>
    change coneExpansion (prefixes n)=Icc ((1/2:ℝ)^(n+1)) 1
    rw [ih,actual_continuous_domain_cone_step_has_the_true_interval_formula
      _ (pow_pos (by norm_num) _) (pow_le_one₀ (by norm_num) (by norm_num))]
    congr 1
    rw [pow_succ]
    ring

theorem actual_continuous_safeopt_iteration_strictly_expands_at_every_time
    (n : ℕ) : prefixes n⊂prefixes (n+1) := by
  rw [actual_every_continuous_safeopt_prefix_is_the_true_closed_interval,
    actual_every_continuous_safeopt_prefix_is_the_true_closed_interval]
  have hp : 0<(1/2:ℝ)^n := pow_pos (by norm_num) _
  have hnext : (1/2:ℝ)^(n+1)<(1/2:ℝ)^n := by rw [pow_succ];nlinarith
  constructor
  · intro x hx
    exact ⟨hnext.le.trans hx.1,hx.2⟩
  · intro h
    have hm : (1/2:ℝ)^(n+1)∈Icc ((1/2:ℝ)^(n+1)) 1 :=
      ⟨le_rfl,pow_le_one₀ (by norm_num) (by norm_num)⟩
    exact not_le_of_gt hnext (h hm).1

theorem actual_every_prefix_is_compact_and_inside_the_compact_safe_domain
    (n : ℕ) : IsCompact (prefixes n) ∧ prefixes n⊆safeDomain ∧
      prefixes (n+1)≠prefixes n := by
  rw [actual_every_continuous_safeopt_prefix_is_the_true_closed_interval]
  refine ⟨isCompact_Icc,?_,?_⟩
  · intro x hx
    exact ⟨(pow_nonneg (by norm_num) _).trans hx.1,hx.2⟩
  · intro he
    have hs := actual_continuous_safeopt_iteration_strictly_expands_at_every_time n
    rw [actual_every_continuous_safeopt_prefix_is_the_true_closed_interval] at hs
    exact hs.2 (by rw [he])

theorem actual_all_round_safeopt_union_is_the_half_open_interval :
    (⋃n,prefixes n)=Ioc (0:ℝ) 1 := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    rw [actual_every_continuous_safeopt_prefix_is_the_true_closed_interval] at hn
    exact ⟨(pow_pos (by norm_num) n).trans_le hn.1,hn.2⟩
  · intro hx
    have ht := tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
    obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hx.1)).exists
    apply mem_iUnion.mpr
    refine ⟨n,?_⟩
    rw [actual_every_continuous_safeopt_prefix_is_the_true_closed_interval]
    exact ⟨hn.le,hx.2⟩

theorem actual_algorithmic_safeopt_closure_is_the_true_least_fixedpoint :
    IsLeast {Y : Set ℝ | seed⊆Y ∧ coneExpansion Y=Y} (Ioc (0:ℝ) 1) := by
  have hseed : seed⊆Ioc (0:ℝ) 1 := by
    intro x hx
    change x=1 at hx
    subst x
    norm_num
  have hfixed : coneExpansion (Ioc (0:ℝ) 1)=Ioc (0:ℝ) 1 := by
    ext x
    constructor
    · rintro (hx | ⟨hdom,y,hy,hcone⟩)
      · exact hx
      · have hb := neg_le_abs (x-y)
        unfold safetyValue at hcone
        exact ⟨by linarith [hy.1],hdom.2⟩
    · exact fun hx=>Or.inl hx
  refine ⟨⟨hseed,hfixed⟩,?_⟩
  intro Y hY x hx
  have hu : x∈⋃n,prefixes n := by rwa [actual_all_round_safeopt_union_is_the_half_open_interval]
  obtain ⟨n,hn⟩ := mem_iUnion.mp hu
  exact actual_every_prefixed_superset_bounds_all_increasing_iterates coneExpansion
    actual_continuous_domain_cone_expansion_is_monotone seed Y hY.1 (le_of_eq hY.2) n hn

theorem actual_safe_zero_is_unreachable_but_belongs_to_topological_closure :
    safetyValue 0=0 ∧ 0∈safeDomain ∧ 0∉(⋃n,prefixes n) ∧
      closure (⋃n,prefixes n)=Icc (0:ℝ) 1 ∧
      0∈closure (⋃n,prefixes n) ∧ (⋃n,prefixes n)≠closure (⋃n,prefixes n) := by
  rw [actual_all_round_safeopt_union_is_the_half_open_interval,
    closure_Ioc (by norm_num : (0:ℝ)≠1)]
  refine ⟨by norm_num [safetyValue],by norm_num [safeDomain],by norm_num,rfl,
    by norm_num,?_⟩
  intro h
  have hm : (0:ℝ)∈Icc 0 1 := by norm_num
  rw [←h] at hm
  norm_num at hm

end SafeLearning.CompleteFoundationsContinuousConeExpansion
