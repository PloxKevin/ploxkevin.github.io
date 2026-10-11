import SafeLearning.CompleteFoundationsMinimaModels
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsCoercivityMargin24

theorem actual_norm_coercivity_is_a_true_cocompact_limit
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (S : Set E) (f : E → ℝ)
    (hc : ∀ M : ℝ,∃ R : ℝ,∀ x ∈ S,R≤‖x‖ → M≤f x) :
    Tendsto f (cocompact E ⊓ 𝓟 S) atTop := by
  apply tendsto_atTop.2
  intro M
  obtain ⟨R,hR⟩ := hc M
  have hn : ∀ᶠ x in cocompact E,R≤‖x‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop R)
  filter_upwards [hn.filter_mono inf_le_left,
    (show ∀ᶠ x in 𝓟 S,x∈S from eventually_principal.mpr (fun _ h=>h)).filter_mono inf_le_right]
    with x hnorm hS
  exact hR x hS hnorm

theorem actual_closed_coercive_sublevels_are_compact
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (S : Set E) (hS : IsClosed S) (f : E → ℝ) (hf : Continuous f)
    (hc : ∀ M : ℝ,∃ R : ℝ,∀ x ∈ S,R≤‖x‖ → M≤f x) (c : ℝ) :
    IsCompact (S ∩ {x | f x≤c}) := by
  have ht := actual_norm_coercivity_is_a_true_cocompact_limit S f hc
  have h := ht.eventually (eventually_ge_atTop (c+1))
  rcases (hasBasis_cocompact.inf_principal S).eventually_iff.1 h with ⟨K,hK,hbound⟩
  apply hK.of_isClosed_subset (hS.inter (isClosed_le hf continuous_const))
  intro x hx
  by_contra hn
  have hd := hbound ⟨hn,hx.1⟩
  have hl : f x≤c := hx.2
  linarith

theorem actual_norm_coercive_continuous_function_attains_on_every_nonempty_closed_set
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (S : Set E) (hS : IsClosed S) (hne : S.Nonempty)
    (f : E → ℝ) (hf : Continuous f)
    (hc : ∀ M : ℝ,∃ R : ℝ,∀ x ∈ S,R≤‖x‖ → M≤f x) :
    ∃ x∈S,IsMinOn f S x := by
  obtain ⟨x₀,hx₀⟩ := hne
  exact SafeLearning.CompleteFoundationsMinimaModels.actual_closed_coercive_minimum
    S hS x₀ hx₀ f hf.continuousOn
    (actual_norm_coercivity_is_a_true_cocompact_limit S f hc)

theorem actual_shifted_squared_norm_is_genuinely_coercive
    {E : Type*} [NormedAddCommGroup E] (nominal : E) :
    ∀ M : ℝ,∃ R : ℝ,∀ u : E,R≤‖u‖ → M≤‖u-nominal‖^2 := by
  intro M
  refine ⟨max 0 M+‖nominal‖+1,?_⟩
  intro u hu
  have h := norm_sub_norm_le u nominal
  have hmax0 : 0≤max 0 M := le_max_left _ _
  have hmaxM : M≤max 0 M := le_max_right _ _
  nlinarith [norm_nonneg (u-nominal)]

theorem actual_affine_safety_filter_attains_on_its_nonempty_halfspace
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
    (a : ℝ) (b nominal : E) (hne : ({u : E | 0≤a+inner ℝ b u}).Nonempty) :
    ∃ u∈{u : E | 0≤a+inner ℝ b u},
      IsMinOn (fun v : E=>‖v-nominal‖^2) {v : E | 0≤a+inner ℝ b v} u := by
  apply actual_norm_coercive_continuous_function_attains_on_every_nonempty_closed_set
    _ (isClosed_le continuous_const (continuous_const.add (continuous_const.inner continuous_id)))
    hne _ ((continuous_id.sub continuous_const).norm.pow 2)
  intro M
  obtain ⟨R,hR⟩ := actual_shifted_squared_norm_is_genuinely_coercive nominal M
  exact ⟨R,fun u _ hu=>hR u hu⟩

theorem actual_nonzero_linear_objective_is_unbounded_and_has_no_maximizer
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (b : E) (hb : b≠0) :
    (∀ M : ℝ,∃ u : E,M<inner ℝ b u) ∧
      ¬∃ u : E,∀ v : E,inner ℝ b v≤inner ℝ b u := by
  have hp : 0<inner ℝ b b := real_inner_self_pos.mpr hb
  have hne : inner ℝ b b≠0 := ne_of_gt hp
  have h (M : ℝ) : M<inner ℝ b (((M+1)/inner ℝ b b) • b) := by
    rw [inner_smul_right,div_mul_cancel₀ _ hne]
    linarith
  refine ⟨fun M=>⟨_,h M⟩,?_⟩
  rintro ⟨u,hu⟩
  exact (not_le.mpr (h (inner ℝ b u))) (hu _)

theorem actual_every_nonempty_compact_set_away_from_zero_has_a_positive_attained_margin
    {E : Type*} [TopologicalSpace E] [Zero E]
    (V : E → ℝ) (hV : Continuous V) (hzero : V 0=0)
    (hpos : ∀ x : E,x≠0 → 0<V x) (K : Set E)
    (hK : IsCompact K) (hne : K.Nonempty) (h0 : (0:E)∉K) :
    V 0=0 ∧ ∃ x∈K,IsLeast (V '' K) (V x) ∧ 0<V x := by
  obtain ⟨x,hx,hm⟩ := hK.exists_isMinOn hne hV.continuousOn
  have hx0 : x≠0 := by rintro rfl;exact h0 hx
  refine ⟨hzero,x,hx,⟨⟨x,hx,rfl⟩,?_⟩,hpos x hx0⟩
  rintro y ⟨z,hz,rfl⟩
  exact hm hz

end SafeLearning.CompleteFoundationsCoercivityMargin24
