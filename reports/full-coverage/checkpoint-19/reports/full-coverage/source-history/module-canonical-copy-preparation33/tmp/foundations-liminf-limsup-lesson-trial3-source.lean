import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsLiminfLimsupLesson

def tailSup (a : ℕ → EReal) (T : ℕ) : EReal := ⨆ t ≥ T, a t
def tailInf (a : ℕ → EReal) (T : ℕ) : EReal := ⨅ t ≥ T, a t

theorem actual_tail_suprema_decrease_and_tail_infima_increase (a : ℕ → EReal) :
    Antitone (tailSup a) ∧ Monotone (tailInf a) := by
  constructor
  · intro T U hTU
    apply iSup_le
    intro t
    apply iSup_le
    intro hut
    exact le_iSup_of_le t (le_iSup_of_le (hTU.trans hut) le_rfl)
  · intro T U hTU
    apply le_iInf
    intro t
    apply le_iInf
    intro hut
    exact iInf_le_of_le t (iInf_le_of_le (hTU.trans hut) le_rfl)

theorem actual_limsup_and_liminf_are_the_extrema_of_the_actual_tail_extrema
    (a : ℕ → EReal) :
    limsup a atTop = ⨅ T, tailSup a T ∧ liminf a atTop = ⨆ T, tailInf a T :=
  ⟨limsup_eq_iInf_iSup_of_nat,liminf_eq_iSup_iInf_of_nat⟩

theorem actual_tail_extrema_have_the_printed_extended_real_limits (a : ℕ → EReal) :
    Tendsto (tailSup a) atTop (𝓝 (limsup a atTop)) ∧
      Tendsto (tailInf a) atTop (𝓝 (liminf a atTop)) := by
  have h := actual_tail_suprema_decrease_and_tail_infima_increase a
  constructor
  · simpa only [(actual_limsup_and_liminf_are_the_extrema_of_the_actual_tail_extrema a).1]
      using tendsto_atTop_iInf h.1
  · simpa only [(actual_limsup_and_liminf_are_the_extrema_of_the_actual_tail_extrema a).2]
      using tendsto_atTop_iSup h.2

theorem actual_real_convergence_iff_equal_finite_liminf_and_limsup
    (a : ℕ → ℝ) (l : ℝ) :
    Tendsto a atTop (𝓝 l) ↔
      liminf (fun n => (a n : EReal)) atTop = (l : EReal) ∧
      limsup (fun n => (a n : EReal)) atTop = (l : EReal) := by
  constructor
  · intro h
    have he := EReal.tendsto_coe.mpr h
    exact ⟨he.liminf_eq,he.limsup_eq⟩
  · rintro ⟨hi,hs⟩
    exact EReal.tendsto_coe.mp (tendsto_of_liminf_eq_limsup hi hs)

theorem actual_real_limit_exists_iff_the_two_extended_limits_agree_at_a_finite_value
    (a : ℕ → ℝ) :
    (∃ l : ℝ, Tendsto a atTop (𝓝 l)) ↔
      ∃ l : ℝ, liminf (fun n => (a n : EReal)) atTop = (l : EReal) ∧
        limsup (fun n => (a n : EReal)) atTop = (l : EReal) := by
  simp only [actual_real_convergence_iff_equal_finite_liminf_and_limsup]

theorem actual_liminf_constraint_is_exactly_the_eventual_epsilon_lower_bound
    (a : ℕ → ℝ) (c : ℝ) :
    (c : EReal) ≤ liminf (fun n => (a n : EReal)) atTop ↔
      ∀ epsilon : ℝ, 0 < epsilon → ∃ T : ℕ, ∀ t ≥ T, c-epsilon ≤ a t := by
  constructor
  · intro h epsilon he
    have hl : ((c-epsilon : ℝ) : EReal) < liminf (fun n => (a n : EReal)) atTop :=
      (EReal.coe_lt_coe_iff.mpr (by linarith)).trans_le h
    have ht := eventually_lt_of_lt_liminf hl
    obtain ⟨T,hT⟩ := eventually_atTop.mp ht
    exact ⟨T,fun t ht => (EReal.coe_lt_coe_iff.mp (hT t ht)).le⟩
  · intro h
    apply (le_liminf_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
    intro y hy
    obtain ⟨b,hyb,hbc⟩ := EReal.exists_between_coe_real hy
    have hb : b < c := EReal.coe_lt_coe_iff.mp hbc
    obtain ⟨T,hT⟩ := h (c-b) (by linarith)
    apply eventually_atTop.mpr
    refine ⟨T,?_⟩
    intro t ht
    have ha : b ≤ a t := by have hg := hT t ht;linarith
    exact hyb.trans_le (EReal.coe_le_coe_iff.mpr ha)

theorem actual_liminf_constraint_can_hold_with_every_term_strictly_below_the_threshold
    (c : ℝ) :
    (∀ n : ℕ, c-1/((n:ℝ)+1)<c) ∧
      Tendsto (fun n : ℕ => c-1/((n:ℝ)+1)) atTop (𝓝 c) ∧
      liminf (fun n : ℕ => ((c-1/((n:ℝ)+1):ℝ) : EReal)) atTop = (c : EReal) := by
  have hden : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hden using 1 <;>
      simp only [one_div,Function.comp_def]
  have hlim : Tendsto (fun n : ℕ => c-1/((n:ℝ)+1)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.sub hzero
  refine ⟨?_,hlim,(EReal.tendsto_coe.mpr hlim).liminf_eq⟩
  intro n
  have hpos : 0 < 1/((n:ℝ)+1) := by positivity
  linarith

end SafeLearning.CompleteFoundationsLiminfLimsupLesson
