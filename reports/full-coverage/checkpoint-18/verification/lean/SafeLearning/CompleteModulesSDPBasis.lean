import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
open Matrix
namespace SafeLearning.CompleteModulesSDPBasis

variable {Index : Type*}

def actualSymmetricMatrix (coordinate : Sym2 Index→ℝ) : Matrix Index Index ℝ :=
  fun row column => coordinate s(row,column)

def actualCoordinatesOfSymmetricMatrix (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    Sym2 Index→ℝ :=
  Sym2.lift ⟨fun row column => matrix row column,
    fun row column => by simpa using hsymmetric.apply column row⟩

theorem actual_unordered_pair_coordinates_always_form_a_symmetric_matrix
    (coordinate : Sym2 Index→ℝ) : (actualSymmetricMatrix coordinate).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro row column
  simp [actualSymmetricMatrix,Sym2.eq_swap]

theorem actual_every_symmetric_matrix_has_the_true_unordered_pair_coordinates
    (matrix : Matrix Index Index ℝ) (hsymmetric : matrix.IsHermitian) :
    actualSymmetricMatrix (actualCoordinatesOfSymmetricMatrix matrix hsymmetric)=matrix := by
  ext row column
  rfl

theorem actual_symmetric_matrix_coordinates_are_unique
    (first second : Sym2 Index→ℝ) (h : actualSymmetricMatrix first=actualSymmetricMatrix second) :
    first=second := by
  funext pair
  induction pair using Sym2.inductionOn with
  | _ row column => exact congrArg (fun matrix : Matrix Index Index ℝ => matrix row column) h

variable [Fintype Index] [DecidableEq Index]

def actualSymmetricCoordinateBasis (pair : Sym2 Index) : Matrix Index Index ℝ :=
  fun row column => if s(row,column)=pair then 1 else 0

theorem actual_symmetric_coordinate_expansion_is_the_true_full_matrix
    (coordinate : Sym2 Index→ℝ) :
    actualSymmetricMatrix coordinate=∑ pair,coordinate pair • actualSymmetricCoordinateBasis pair := by
  ext row column
  simp [actualSymmetricMatrix,actualSymmetricCoordinateBasis,Matrix.sum_apply,Matrix.smul_apply,eq_comm]

theorem actual_symmetric_basis_coefficients_are_unique_in_the_true_full_matrix_sum
    (first second : Sym2 Index→ℝ)
    (h : (∑ pair,first pair • actualSymmetricCoordinateBasis pair)=
      ∑ pair,second pair • actualSymmetricCoordinateBasis pair) : first=second := by
  apply actual_symmetric_matrix_coordinates_are_unique first second
  simpa only [actual_symmetric_coordinate_expansion_is_the_true_full_matrix] using h

omit [DecidableEq Index] in
theorem actual_symmetric_matrix_coordinate_count_is_n_times_n_plus_one_over_two :
    Fintype.card (Sym2 Index)=Fintype.card Index*(Fintype.card Index+1)/2 := by
  rw [Sym2.card,Nat.choose_two_right]
  simp [Nat.mul_comm]

theorem actual_diagonal_and_offdiagonal_symmetric_coordinate_counts :
    Fintype.card {pair : Sym2 Index // pair.IsDiag}=Fintype.card Index ∧
      Fintype.card {pair : Sym2 Index // ¬pair.IsDiag}=
        Fintype.card Index*(Fintype.card Index-1)/2 := by
  constructor
  · exact Sym2.card_subtype_diag
  · rw [Sym2.card_subtype_not_diag,Nat.choose_two_right]

theorem actual_stein_matrix_is_an_lmi_in_the_true_symmetric_basis_coefficients
    (system : Matrix Index Index ℝ) (coordinate : Sym2 Index→ℝ) :
    actualSymmetricMatrix coordinate-systemᵀ*actualSymmetricMatrix coordinate*system=
      ∑ pair,coordinate pair •
        (actualSymmetricCoordinateBasis pair-systemᵀ*actualSymmetricCoordinateBasis pair*system) := by
  rw [actual_symmetric_coordinate_expansion_is_the_true_full_matrix]
  simp only [Matrix.mul_sum,Matrix.sum_mul,Matrix.mul_smul,Matrix.smul_mul,
    smul_sub,Finset.sum_sub_distrib]

theorem actual_two_by_two_symmetric_matrix_has_the_three_literal_source_basis_matrices
    (first second third : ℝ) :
    (!![first,second;second,third] : Matrix (Fin 2) (Fin 2) ℝ)=
      first • (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℝ)+
      second • (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℝ)+
      third • (!![0,0;0,1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext row column
  fin_cases row <;> fin_cases column <;> simp

theorem actual_two_by_two_basis_has_exactly_three_independent_unknowns :
    Fintype.card (Sym2 (Fin 2))=3 := by
  rw [actual_symmetric_matrix_coordinate_count_is_n_times_n_plus_one_over_two]
  norm_num

end SafeLearning.CompleteModulesSDPBasis
