import SafeLearning.CompleteModulesNNTanhOffset24
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNTanhOffsetConsequences24
open CompleteModulesNNTanhOffset24 CompleteModulesTanhNumerics CompleteModulesTanhChords
open CompleteModulesLipSDP

theorem actual_literal_diagonal_products_are_nonnegative_rounded_and_not_equal :
    0 ≤ (-1:ℝ) * sourceChannel 0 (-1) ∧
    0 ≤ (-1.5:ℝ) * sourceChannel 1 (-1.5) ∧
    |(-1:ℝ)*sourceChannel 0 (-1)-0.762|<0.0005 ∧
    (-1:ℝ)*sourceChannel 0 (-1)≠0.762 ∧
    |(-1.5:ℝ)*sourceChannel 1 (-1.5)-0.753|<0.0005 ∧
    (-1.5:ℝ)*sourceChannel 1 (-1.5)≠0.753 := by
  have h:=actual_tanh_one_rigorous_rational_enclosure
  have hh:=actual_half_and_two_tanh_have_rigorous_rational_enclosures
  norm_num [sourceChannel,sourceBase,shifted,Real.tanh_neg]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first | (apply abs_lt.mpr; constructor <;> linarith) | (intro he; linarith) | linarith

theorem actual_full_block_sector_box_certificate_applies_to_all_offset_channels
    {n : Type*} [Fintype n] (centers v : n→ℝ)
    (Q : Matrix (n⊕n) (n⊕n) ℝ)
    (hQ : ∀ d : n→ℝ, (∀ i, 0≤d i ∧ d i≤1) →
      0≤ quadratic Q (Sum.elim v (fun i=>d i*v i))) :
    0≤quadratic Q (Sum.elim v (fun i=>shifted (centers i) (v i))) := by
  have hgain : ∀ i, ∃ d : ℝ, 0≤d ∧ d≤1 ∧ shifted (centers i) (v i)=d*v i := by
    intro i
    obtain ⟨d,hd0,hd1,hd⟩ :=
      (actual_every_shifted_channel_vanishes_and_has_own_valid_sector (centers i)).2.1 (v i) 0
    refine ⟨d,hd0,hd1,?_⟩
    simpa [shifted] using hd
  choose d hd0 hd1 he using hgain
  simpa only [←he] using hQ d (fun i=>⟨hd0 i,hd1 i⟩)

theorem actual_bias_free_tanh_two_layer_network_has_all_zero_equilibrium_preactivations
    {nx nu n1 n2 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (W2 : Matrix (Fin nu) (Fin n2) ℝ) :
    CompleteModulesNNTwoLayerLFT23.v1 W0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.w1 Real.tanh W0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.v2 Real.tanh W0 W1 0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.w2 Real.tanh W0 W1 0 0 (0 : Fin nx→ℝ)=0 ∧
    CompleteModulesNNTwoLayerLFT23.controller Real.tanh W0 W1 W2 0 0 0 (0 : Fin nx→ℝ)=0 := by
  simp [CompleteModulesNNTwoLayerLFT23.v1,CompleteModulesNNTwoLayerLFT23.w1,
    CompleteModulesNNTwoLayerLFT23.v2,CompleteModulesNNTwoLayerLFT23.w2,
    CompleteModulesNNTwoLayerLFT23.controller,CompleteModulesNNTwoLayerLFT23.activation,
    Function.comp_def,show (fun _ : Fin n1 => (0:ℝ))=0 from rfl,
    show (fun _ : Fin n2 => (0:ℝ))=0 from rfl]

end SafeLearning.CompleteModulesNNTanhOffsetConsequences24
