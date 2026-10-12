import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteAppliedViabilityPenaltyOrder20

variable {Policy : Type*}

def penalizedValue (gain risk : Policy→ℝ) (penalty : ℝ) : EReal :=
  ⨆ u, ((gain u-penalty*risk u : ℝ) : EReal)
def safeValue (gain : Policy→ℝ) (safe : Set Policy) : EReal :=
  ⨆ u : safe, ((gain u.val : ℝ) : EReal)

theorem actual_each_controller_penalized_return_is_antitone
    (gain risk : Policy→ℝ) (hrisk : ∀u,0≤risk u) (p1 p2 : ℝ) (hp : p1≤p2) (u : Policy) :
    gain u-p2*risk u≤gain u-p1*risk u := by
  have h := mul_le_mul_of_nonneg_right hp (hrisk u)
  linarith

theorem actual_unrestricted_supremum_is_antitone_in_penalty
    (gain risk : Policy→ℝ) (hrisk : ∀u,0≤risk u) : Antitone (penalizedValue gain risk) := by
  intro p1 p2 hp
  apply iSup_mono
  intro u
  exact_mod_cast actual_each_controller_penalized_return_is_antitone gain risk hrisk p1 p2 hp u

theorem actual_every_safe_controller_is_included_and_safe_value_is_a_lower_bound
    (gain risk : Policy→ℝ) (safe : Set Policy) (hzero : ∀u∈safe,risk u=0) (p : ℝ) :
    safeValue gain safe≤penalizedValue gain risk p := by
  apply iSup_le
  intro u
  have h := le_iSup (fun v=>((gain v-p*risk v : ℝ) : EReal)) u.val
  simpa only [penalizedValue,hzero u.val u.property,mul_zero,sub_zero] using h

theorem actual_attained_safe_penalized_optimizer_gives_equality_of_true_values
    (gain risk : Policy→ℝ) (safe : Set Policy) (hzero : ∀u∈safe,risk u=0)
    (p : ℝ) (u : Policy) (hu : u∈safe)
    (hmaximum : ∀v,gain v-p*risk v≤gain u-p*risk u) :
    penalizedValue gain risk p=safeValue gain safe := by
  apply le_antisymm
  · have hup : penalizedValue gain risk p≤((gain u : ℝ) : EReal) := by
      apply iSup_le
      intro v
      have hv : gain v-p*risk v≤gain u := by simpa [hzero u hu] using hmaximum v
      exact_mod_cast hv
    exact hup.trans (le_iSup_of_le (⟨u,hu⟩ : safe) le_rfl)
  · exact actual_every_safe_controller_is_included_and_safe_value_is_a_lower_bound gain risk safe hzero p

end SafeLearning.CompleteAppliedViabilityPenaltyOrder20
