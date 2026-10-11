import SafeLearning.CompleteModulesNNCertificateAudit23
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
open scoped BigOperators

namespace SafeLearning.CompleteModulesNNTwoLayerLFT23

abbrev State (nx : ℕ) := Fin nx → ℝ
abbrev Neurons (n1 n2 : ℕ) := Fin n1 ⊕ Fin n2
abbrev Stack (nx n1 n2 : ℕ) := Fin nx ⊕ Neurons n1 n2

def Nux (nu nx : ℕ) : Matrix (Fin nu) (Fin nx) ℝ := 0
def Nuw {nu n1 n2 : ℕ} (W2 : Matrix (Fin nu) (Fin n2) ℝ) :
    Matrix (Fin nu) (Neurons n1 n2) ℝ := Matrix.fromCols 0 W2
def Nvx {nx n1 n2 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ) :
    Matrix (Neurons n1 n2) (Fin nx) ℝ := Matrix.fromRows W0 0
def Nvw {n1 n2 : ℕ} (W1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Matrix (Neurons n1 n2) (Neurons n1 n2) ℝ := Matrix.fromBlocks 0 0 W1 0

def RV {nx nu n1 n2 : ℕ} (W2 : Matrix (Fin nu) (Fin n2) ℝ) :
    Matrix (Fin nx ⊕ Fin nu) (Stack nx n1 n2) ℝ :=
  Matrix.fromBlocks 1 0 (Nux nu nx) (Nuw W2)
def Rphi {nx n1 n2 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) :
    Matrix (Neurons n1 n2 ⊕ Neurons n1 n2) (Stack nx n1 n2) ℝ :=
  Matrix.fromBlocks (Nvx W0) (Nvw W1) 0 1

def activation {n : ℕ} (phi : ℝ → ℝ) (v : Fin n → ℝ) : Fin n → ℝ := phi ∘ v
def v1 {nx n1 : ℕ} (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (b0 : Fin n1 → ℝ) (x : State nx) := W0.mulVec x+b0
def w1 {nx n1 : ℕ} (phi : ℝ → ℝ) (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (b0 : Fin n1 → ℝ) (x : State nx) := activation phi (v1 W0 b0 x)
def v2 {nx n1 n2 : ℕ} (phi : ℝ → ℝ) (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ)
    (x : State nx) := W1.mulVec (w1 phi W0 b0 x)+b1
def w2 {nx n1 n2 : ℕ} (phi : ℝ → ℝ) (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ)
    (x : State nx) := activation phi (v2 phi W0 W1 b0 b1 x)
def controller {nx nu n1 n2 : ℕ} (phi : ℝ → ℝ)
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ) (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ)
    (b2 : Fin nu → ℝ) (x : State nx) := W2.mulVec (w2 phi W0 W1 b0 b1 x)+b2

theorem actual_block_lower_triangular_entries {n1 n2 : ℕ}
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) :
    (∀ i j : Fin n1, Nvw W1 (.inl i) (.inl j)=0) ∧
    (∀ (i : Fin n1) (j : Fin n2), Nvw W1 (.inl i) (.inr j)=0) ∧
    (∀ (i : Fin n2) (j : Fin n1), Nvw W1 (.inr i) (.inl j)=W1 i j) ∧
    (∀ i j : Fin n2, Nvw W1 (.inr i) (.inr j)=0) := by
  simp [Nvw]

theorem actual_N_maps_are_the_printed_blocks {nx nu n1 n2 : ℕ}
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ) (x : State nx)
    (first : Fin n1 → ℝ) (second : Fin n2 → ℝ) :
    (Nuw W2).mulVec (Sum.elim first second)=W2.mulVec second ∧
    (Nvx W0).mulVec x=Sum.elim (W0.mulVec x) (0 : Fin n2 → ℝ) ∧
    (Nvw W1).mulVec (Sum.elim first second)=Sum.elim (0 : Fin n1 → ℝ) (W1.mulVec first) := by
  simp [Nuw,Nvx,Nvw,Matrix.fromCols_mulVec,Matrix.fromRows_mulVec,Matrix.fromBlocks_mulVec]

theorem actual_affine_LFT_equations {nx nu n1 n2 : ℕ} (phi : ℝ → ℝ)
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ) (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ)
    (b2 : Fin nu → ℝ) (x : State nx) :
    controller phi W0 W1 W2 b0 b1 b2 x =
      (Nux nu nx).mulVec x+(Nuw W2).mulVec
        (Sum.elim (w1 phi W0 b0 x) (w2 phi W0 W1 b0 b1 x))+b2 ∧
    Sum.elim (v1 W0 b0 x) (v2 phi W0 W1 b0 b1 x)=
      (Nvx W0).mulVec x+(Nvw W1).mulVec
        (Sum.elim (w1 phi W0 b0 x) (w2 phi W0 W1 b0 b1 x))+Sum.elim b0 b1 := by
  rw [(actual_N_maps_are_the_printed_blocks W0 W1 W2 x
    (w1 phi W0 b0 x) (w2 phi W0 W1 b0 b1 x)).1,
    (actual_N_maps_are_the_printed_blocks W0 W1 W2 x
    (w1 phi W0 b0 x) (w2 phi W0 W1 b0 b1 x)).2.1,
    (actual_N_maps_are_the_printed_blocks W0 W1 W2 x
    (w1 phi W0 b0 x) (w2 phi W0 W1 b0 b1 x)).2.2]
  constructor
  · simp [controller,Nux]
  · funext i; cases i <;> simp [v1,v2]

theorem actual_arbitrary_activation_forward_substitution_is_the_unique_solution
    {nx n1 n2 : ℕ} (phi : ℝ → ℝ) (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ)
    (x : State nx) :
    ∃! w : (Fin n1 → ℝ) × (Fin n2 → ℝ),
      w.1=activation phi (W0.mulVec x+b0) ∧
      w.2=activation phi (W1.mulVec w.1+b1) := by
  refine ⟨⟨w1 phi W0 b0 x,w2 phi W0 W1 b0 b1 x⟩,⟨rfl,rfl⟩,?_⟩
  intro w hw
  apply Prod.ext
  · exact hw.1
  · simpa [hw.1,w2,w1,v1] using hw.2

theorem actual_RV_and_Rphi_actions {nx nu n1 n2 : ℕ}
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ) (x : State nx)
    (first : Fin n1 → ℝ) (second : Fin n2 → ℝ) :
    (RV W2).mulVec (Sum.elim x (Sum.elim first second))=
      Sum.elim x (W2.mulVec second) ∧
    (Rphi W0 W1).mulVec (Sum.elim x (Sum.elim first second))=
      Sum.elim (Sum.elim (W0.mulVec x) (W1.mulVec first)) (Sum.elim first second) := by
  constructor
  · simp [RV,Nux,Nuw,Matrix.fromBlocks_mulVec,Matrix.fromCols_mulVec]
  · simp [Rphi,Nvx,Nvw,Matrix.fromBlocks_mulVec,Matrix.fromRows_mulVec]
    funext i; cases i with
    | inl i => cases i <;> simp
    | inr i => rfl

def stabilityMatrix {nx nu n1 n2 : ℕ}
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (W1 : Matrix (Fin n2) (Fin n1) ℝ)
    (W2 : Matrix (Fin nu) (Fin n2) ℝ)
    (linear : Matrix (Fin nx ⊕ Fin nu) (Fin nx ⊕ Fin nu) ℝ)
    (qc : Matrix (Neurons n1 n2 ⊕ Neurons n1 n2) (Neurons n1 n2 ⊕ Neurons n1 n2) ℝ) :
    Matrix (Stack nx n1 n2) (Stack nx n1 n2) ℝ :=
  (RV (nx:=nx) (n1:=n1) W2).transpose*linear*(RV (nx:=nx) (n1:=n1) W2)+
    (Rphi W0 W1).transpose*qc*(Rphi W0 W1)

def containmentMatrix {nx n1 : ℕ} (P : Matrix (Fin nx) (Fin nx) ℝ)
    (W0 : Matrix (Fin n1) (Fin nx) ℝ) (radius : Fin n1 → ℝ) (i : Fin n1) :
    Matrix (Unit ⊕ Fin nx) (Unit ⊕ Fin nx) ℝ :=
  Matrix.fromBlocks (fun _ _ => (radius i)^2) (fun _ j => W0 i j)
    (fun j _ => W0 i j) P

theorem actual_LMI_dimensions_and_independent_parameter_count (nx n1 n2 : ℕ) :
    Fintype.card (Stack nx n1 n2)=nx+n1+n2 ∧
    Fintype.card (Sym2 (Fin nx) ⊕ Neurons n1 n2)=nx*(nx+1)/2+n1+n2 ∧
    Fintype.card (Fin n1)=n1 ∧ Fintype.card (Unit ⊕ Fin nx)=1+nx := by
  simp [Stack,Neurons,Sym2.card,Nat.choose_two_right,Nat.mul_comm,Nat.add_assoc]

def storageCoordinateEquiv
    (nx : ℕ) :
    {P : Matrix (Fin nx) (Fin nx) ℝ // ∀ i j,P i j=P j i} ≃
      (Sym2 (Fin nx) → ℝ) := Sym2.lift

theorem actual_symmetric_storage_coefficients_are_exactly_the_free_unordered_entries
    (nx : ℕ) : Function.Bijective (storageCoordinateEquiv nx) :=
  (storageCoordinateEquiv nx).bijective

theorem actual_output_feedback_replaces_first_weight_by_the_matrix_product
    {nx ny n1 : ℕ} (W0 : Matrix (Fin n1) (Fin ny) ℝ)
    (C : Matrix (Fin ny) (Fin nx) ℝ) (b0 : Fin n1 → ℝ) (x : State nx) :
    v1 W0 b0 (C.mulVec x)=v1 (W0*C) b0 x := by
  simp [v1,Matrix.mulVec_mulVec]

theorem actual_bias_columns_cancel_in_equilibrium_deviations
    {nx nu n1 n2 : ℕ} (A : Matrix (Fin nx) (Fin nx) ℝ)
    (B : Matrix (Fin nx) (Fin nu) ℝ) (W0 : Matrix (Fin n1) (Fin nx) ℝ)
    (W1 : Matrix (Fin n2) (Fin n1) ℝ) (W2 : Matrix (Fin nu) (Fin n2) ℝ)
    (b0 : Fin n1 → ℝ) (b1 : Fin n2 → ℝ) (b2 : Fin nu → ℝ)
    (x xs : State nx) (first firsts : Fin n1 → ℝ) (second seconds : Fin n2 → ℝ)
    (heq : xs=A.mulVec xs+B.mulVec (W2.mulVec seconds+b2)) :
    ((A.mulVec x+B.mulVec (W2.mulVec second+b2))-xs)=
      A.mulVec (x-xs)+B.mulVec (W2.mulVec (second-seconds)) ∧
    (W0.mulVec x+b0)-(W0.mulVec xs+b0)=W0.mulVec (x-xs) ∧
    (W1.mulVec first+b1)-(W1.mulVec firsts+b1)=W1.mulVec (first-firsts) ∧
    (W2.mulVec second+b2)-(W2.mulVec seconds+b2)=W2.mulVec (second-seconds) := by
  constructor
  · conv_lhs => rw [heq]
    simp only [Matrix.mulVec_sub,Matrix.mulVec_add]
    module
  · constructor
    · simp only [Matrix.mulVec_sub]; module
    · constructor <;> (simp only [Matrix.mulVec_sub]; module)

def shifted (phi : ℝ → ℝ) (base s : ℝ) : ℝ := phi (s+base)-phi base

theorem actual_shifted_neuron_equation_and_inherited_common_slopes
    (phi : ℝ → ℝ) (base : ℝ) (a b : ℝ)
    (hs : SafeLearning.CompleteModulesLipSDP.slopeRestricted phi a b) :
    shifted phi base 0=0 ∧
    SafeLearning.CompleteModulesLipSDP.slopeRestricted (shifted phi base) a b ∧
    (∀ v : ℝ,phi v-phi base=shifted phi base (v-base)) ∧
    (∀ v : ℝ,0 ≤ 2*(shifted phi base v-a*v)*(b*v-shifted phi base v)) := by
  have hshift : SafeLearning.CompleteModulesLipSDP.slopeRestricted (shifted phi base) a b := by
    intro x y
    obtain ⟨d,hda,hdb,hd⟩ := hs (x+base) (y+base)
    refine ⟨d,hda,hdb,?_⟩
    dsimp [shifted]
    convert hd using 1 <;> ring
  refine ⟨by simp [shifted],hshift,?_,?_⟩
  · intro v; simp [shifted]
  · intro v
    have h := SafeLearning.CompleteModulesLipSDP.scalar_slope_quadratic_constraint
      (shifted phi base) a b hshift v 0
    simp [shifted] at h
    dsimp [shifted]
    nlinarith [h]

theorem actual_equal_offsets_share_the_same_shifted_nonlinearity
    (phi : ℝ → ℝ) (first second : ℝ) (heq : first=second) :
    shifted phi first=shifted phi second := by rw [heq]

theorem actual_unequal_offsets_can_destroy_a_repeated_nonlinearity :
    shifted (fun s : ℝ => max s 0) 1 ≠ shifted (fun s : ℝ => max s 0) (-1) := by
  intro he
  have hv := congrFun he (1/2)
  norm_num [shifted] at hv

end SafeLearning.CompleteModulesNNTwoLayerLFT23
