import SafeLearning.CompleteModulesNNTwoLayerLFT23
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesNNTwoLayerLFTConsequences23
open SafeLearning.CompleteModulesNNTwoLayerLFT23

def augmentedMatrix {nx nu n1 n2 : ℕ}
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ)
    (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ) (b2 : Fin nu → ℝ) :
    Matrix (Fin nu ⊕ Neurons n1 n2) (Stack nx n1 n2 ⊕ Unit) ℝ :=
  Matrix.fromCols (Matrix.fromBlocks (Nux nu nx) (Nuw W2) (Nvx W0) (Nvw W1))
    (Matrix.of (fun i (_ : Unit) => Sum.elim b2 (Sum.elim b0 b1) i))

theorem actual_augmented_homogeneous_coordinate_matrix_has_the_printed_action
    {nx nu n1 n2 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (W2 : Matrix (Fin nu) (Fin n2) ℝ)
    (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ) (b2 : Fin nu → ℝ)
    (x : State nx) (first : Fin n1 → ℝ) (second : Fin n2 → ℝ) :
    (augmentedMatrix W0 W1 W2 b0 b1 b2).mulVec
      (Sum.elim (Sum.elim x (Sum.elim first second)) (fun _ : Unit => 1)) =
    Sum.elim (W2.mulVec second+b2)
      (Sum.elim (W0.mulVec x+b0) (W1.mulVec first+b1)) := by
  unfold augmentedMatrix
  rw [Matrix.fromCols_mulVec_sumElim,Matrix.fromBlocks_mulVec]
  simp [Nux,Nuw,Nvx,Nvw,Matrix.fromCols_mulVec_sumElim,
    Matrix.fromRows_mulVec,Matrix.fromBlocks_mulVec]
  funext i
  cases i with
  | inl i => simp [Matrix.mulVec,dotProduct]
  | inr i => cases i <;> simp [Matrix.mulVec,dotProduct]

theorem actual_plant_substitution_is_the_printed_matrix_product
    {nx nu n2 : ℕ} (A : Matrix (Fin nx) (Fin nx) ℝ)
    (B : Matrix (Fin nx) (Fin nu) ℝ) (W2 : Matrix (Fin nu) (Fin n2) ℝ)
    (b2 : Fin nu → ℝ) (x : State nx) (second : Fin n2 → ℝ) :
    A.mulVec x+B.mulVec (W2.mulVec second+b2) =
      A.mulVec x+(B*W2).mulVec second+B.mulVec b2 := by
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec]
  module

theorem actual_local_offset_sector_is_exactly_the_shifted_centered_sector
    (phi : ℝ → ℝ) (base a b : ℝ) (I : Set ℝ) :
    (∀ v ∈ I,0 ≤ (phi v-phi base-a*(v-base))*
      (b*(v-base)-(phi v-phi base))) ↔
    (∀ s ∈ {s : ℝ | s+base ∈ I},0 ≤
      (shifted phi base s-a*s)*(b*s-shifted phi base s)) := by
  constructor
  · intro h s hs
    simpa [shifted] using h (s+base) hs
  · intro h v hv
    have he := h (v-base) (by simpa using hv)
    simpa [shifted] using he

end SafeLearning.CompleteModulesNNTwoLayerLFTConsequences23
