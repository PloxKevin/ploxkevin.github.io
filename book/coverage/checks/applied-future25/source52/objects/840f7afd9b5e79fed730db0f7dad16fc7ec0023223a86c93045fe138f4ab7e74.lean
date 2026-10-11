import SafeLearning.CompleteFoundationsMinimaModels
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsExtremeValueCountermodels24

theorem actual_continuous_functions_attain_both_finite_extrema_on_nonempty_compact_sets
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (hne : K.Nonempty) (f : X → ℝ) (hf : ContinuousOn f K) :
    (∃ x∈K,IsLeast (f '' K) (f x)) ∧
      (∃ x∈K,IsGreatest (f '' K) (f x)) := by
  constructor
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne hf
    refine ⟨x,hx,⟨⟨x,hx,rfl⟩,?_⟩⟩
    rintro y ⟨z,hz,rfl⟩
    exact hm hz
  · obtain ⟨x,hx,hm⟩ := hK.exists_isMaxOn hne hf
    refine ⟨x,hx,⟨⟨x,hx,rfl⟩,?_⟩⟩
    rintro y ⟨z,hz,rfl⟩
    exact hm hz

theorem actual_identity_on_the_half_open_unit_interval_has_inf_zero_but_no_minimum :
    IsGLB ((fun x : ℝ=>x) '' Ioc (0:ℝ) 1) 0 ∧
      ¬∃ x∈Ioc (0:ℝ) 1,IsMinOn (fun y : ℝ=>y) (Ioc (0:ℝ) 1) x := by
  constructor
  · simpa using (isGLB_Ioc (by norm_num : (0:ℝ) < 1))
  · rintro ⟨x,hx,hm⟩
    have hh : x/2∈Ioc (0:ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
    have h := hm hh
    change x ≤ x/2 at h
    linarith [hx.1]

theorem actual_half_open_unit_interval_is_not_closed_and_not_compact :
    ¬IsClosed (Ioc (0:ℝ) 1) ∧ ¬IsCompact (Ioc (0:ℝ) 1) := by
  have hn : ¬IsClosed (Ioc (0:ℝ) 1) := by
    intro hc
    have he := hc.closure_eq
    rw [closure_Ioc (by norm_num : (0:ℝ) ≠ 1)] at he
    have h0 : (0:ℝ)∈Ioc (0:ℝ) 1 := by rw [←he];norm_num
    norm_num at h0
  exact ⟨hn,fun h=>hn h.isClosed⟩

theorem actual_exponential_on_the_unbounded_halfline_has_inf_zero_but_no_minimum :
    Continuous (fun x : ℝ=>Real.exp (-x)) ∧
      IsGLB ((fun x : ℝ=>Real.exp (-x)) '' Ici 0) 0 ∧
      ¬∃ x∈Ici (0:ℝ),IsMinOn (fun y=>Real.exp (-y)) (Ici 0) x := by
  exact ⟨Real.continuous_exp.comp continuous_neg,
    SafeLearning.CompleteFoundationsMinimaModels.actual_exp_infimum_and_no_minimum⟩

theorem actual_closed_halfline_is_unbounded_and_not_compact :
    IsClosed (Ici (0:ℝ)) ∧ ¬Bornology.IsBounded (Ici (0:ℝ)) ∧
      ¬IsCompact (Ici (0:ℝ)) := by
  have hn : ¬Bornology.IsBounded (Ici (0:ℝ)) := by
    intro hb
    obtain ⟨B,hB⟩ := hb.bddAbove
    have hx : max 0 B+1∈Ici (0:ℝ) := by
      change 0 ≤ max 0 B+1
      linarith [le_max_left (0:ℝ) B]
    have hh := hB hx
    have hmax : B ≤ max 0 B := le_max_right _ _
    linarith
  exact ⟨isClosed_Ici,hn,fun h=>hn h.isBounded⟩

def jump (x : ℝ) : ℝ := if x < 1 then x else 0

theorem actual_endpoint_jump_on_the_compact_unit_interval_has_exact_range :
    IsCompact (Icc (0:ℝ) 1) ∧ jump 1=0 ∧ jump '' Icc (0:ℝ) 1=Ico (0:ℝ) 1 := by
  refine ⟨isCompact_Icc,by norm_num [jump],?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    by_cases h : x < 1
    · simpa [jump,h] using (show x∈Ico (0:ℝ) 1 from ⟨hx.1,h⟩)
    · simp [jump,h]
  · intro hy
    refine ⟨y,⟨hy.1,hy.2.le⟩,?_⟩
    simp [jump,hy.2]

theorem actual_endpoint_jump_has_supremum_one_but_no_maximizer :
    IsLUB (jump '' Icc (0:ℝ) 1) 1 ∧
      ¬∃ x∈Icc (0:ℝ) 1,IsMaxOn jump (Icc (0:ℝ) 1) x := by
  constructor
  · rw [actual_endpoint_jump_on_the_compact_unit_interval_has_exact_range.2.2]
    exact isLUB_Ico (by norm_num)
  · rintro ⟨x,hx,hm⟩
    have hr := actual_endpoint_jump_on_the_compact_unit_interval_has_exact_range.2.2
    have hfx : jump x∈Ico (0:ℝ) 1 := by rw [←hr];exact ⟨x,hx,rfl⟩
    have hy : (jump x+1)/2∈Ico (0:ℝ) 1 := by constructor <;> linarith [hfx.1,hfx.2]
    rw [←hr] at hy
    obtain ⟨z,hz,he⟩ := hy
    have hh := hm hz
    change jump z ≤ jump x at hh
    rw [he] at hh
    linarith [hfx.2]

theorem actual_endpoint_jump_is_discontinuous_at_one : ¬ContinuousAt jump 1 := by
  let seq : ℕ → ℝ := fun n=>1-1/((n:ℝ)+1)
  have ht : Tendsto seq atTop (𝓝 1) := by
    simpa [seq] using (tendsto_const_nhds (x:=(1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have he (n : ℕ) : jump (seq n)=seq n := by
    have hp : 0 < 1/((n:ℝ)+1) := by positivity
    have hl : seq n < 1 := by dsimp [seq];linarith
    simp [jump,hl]
  intro hc
  have hz : Tendsto (jump ∘ seq) atTop (𝓝 0) := by
    simpa [show jump 1=0 by norm_num [jump]] using hc.tendsto.comp ht
  have ho : Tendsto (jump ∘ seq) atTop (𝓝 1) := by
    simpa only [Function.comp_def,he] using ht
  have impossible : (0:ℝ)=1 := tendsto_nhds_unique hz ho
  norm_num at impossible

theorem actual_endpoint_jump_not_continuous_on_its_compact_domain :
    ¬ContinuousOn jump (Icc (0:ℝ) 1) := by
  intro hc
  obtain ⟨x,hx,hm⟩ := isCompact_Icc.exists_isMaxOn (by norm_num : (Icc (0:ℝ) 1).Nonempty) hc
  exact actual_endpoint_jump_has_supremum_one_but_no_maximizer.2 ⟨x,hx,hm⟩


theorem actual_extended_real_supremum_on_a_nonempty_compact_set_is_finite_and_attained
    {X : Type*} [TopologicalSpace X] (K : Set X) (hK : IsCompact K)
    (hne : K.Nonempty) (f : X → ℝ) (hf : ContinuousOn f K) :
    ∃ x∈K,sSup ((fun y : X => (f y : EReal)) '' K)=(f x : EReal) := by
  obtain ⟨_,⟨x,hx,hm⟩⟩ :=
    actual_continuous_functions_attain_both_finite_extrema_on_nonempty_compact_sets K hK hne f hf
  have hh : IsGreatest ((fun y : X => (f y : EReal)) '' K) (f x : EReal) := by
    refine ⟨⟨x,hx,rfl⟩,?_⟩
    rintro y ⟨z,hz,rfl⟩
    have h : f z ≤ f x := hm.2 ⟨z,hz,rfl⟩
    change (f z : EReal) ≤ (f x : EReal)
    exact_mod_cast h
  exact ⟨x,hx,hh.isLUB.sSup_eq⟩

theorem actual_compact_subsequence_and_continuity_force_any_extended_value_limit_to_be_finite
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ) (hf : ContinuousOn f K)
    (seq : ℕ → X) (hseq : ∀ n,seq n∈K) (M : EReal)
    (hM : Tendsto (fun n => (f (seq n) : EReal)) atTop (𝓝 M)) :
    ∃ a∈K,∃ phi : ℕ → ℕ,StrictMono phi ∧ Tendsto (seq ∘ phi) atTop (𝓝 a) ∧
      (f a : EReal)=M ∧ M≠⊤ ∧ M≠⊥ := by
  obtain ⟨a,ha,phi,hphi,hlimit⟩ := hK.tendsto_subseq hseq
  have hwithin : Tendsto (seq ∘ phi) atTop (𝓝[K] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlimit,Eventually.of_forall (fun n=>hseq (phi n))⟩
  have hreal : Tendsto f (𝓝[K] a) (𝓝 (f a)) := hf a ha
  have hfinite : Tendsto (fun n => (f (seq (phi n)) : EReal)) atTop (𝓝 (f a : EReal)) :=
    (continuous_coe_real_ereal.tendsto (f a)).comp (hreal.comp hwithin)
  have heq : (f a : EReal)=M := tendsto_nhds_unique hfinite (hM.comp hphi.tendsto_atTop)
  refine ⟨a,ha,phi,hphi,hlimit,heq,?_,?_⟩ <;> rw [←heq] <;> simp

end SafeLearning.CompleteFoundationsExtremeValueCountermodels24
