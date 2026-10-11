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

end SafeLearning.CompleteFoundationsExtremeValueCountermodels24
