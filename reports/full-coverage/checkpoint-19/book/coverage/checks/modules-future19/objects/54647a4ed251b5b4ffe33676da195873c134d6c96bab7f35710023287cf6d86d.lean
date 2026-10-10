import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SafeLearning.CompleteModulesGPNoiselessRepeats

def readings (n : ℕ) (latent : ℝ) : Fin (n+1) → ℝ := fun _ => latent
def observationKernel (n : ℕ) : Kernel ℝ (Fin (n+1) → ℝ) :=
  Kernel.deterministic (readings n) (by unfold readings; fun_prop)
def posteriorKernel (n : ℕ) : Kernel (Fin (n+1) → ℝ) ℝ :=
  Kernel.deterministic (fun y => y 0) (by fun_prop)
def fullJoint (n : ℕ) : Measure (ℝ × (Fin (n+1) → ℝ)) :=
  gaussianReal 0 1 ⊗ₘ observationKernel n
def dataLaw (n : ℕ) : Measure (Fin (n+1) → ℝ) :=
  (gaussianReal 0 1).map (readings n)

theorem actual_any_positive_number_of_noiseless_repeats_has_the_same_exact_conditional_value
    (n : ℕ) : (fullJoint n).map Prod.swap = dataLaw n ⊗ₘ posteriorKernel n := by
  rw [fullJoint, observationKernel, posteriorKernel, Measure.compProd_deterministic,
    Measure.compProd_deterministic, dataLaw,
    Measure.map_map measurable_swap (by unfold readings; fun_prop),
    Measure.map_map (by fun_prop) (by unfold readings; fun_prop)]
  rfl

theorem actual_any_positive_number_of_noiseless_repeats_has_zero_latent_posterior_variance
    (n : ℕ) (latent : ℝ) :
    posteriorKernel n (readings n latent) = Measure.dirac latent ∧
      Var[id; posteriorKernel n (readings n latent)] = 0 := by
  constructor
  · rfl
  · exact variance_dirac latent

theorem actual_already_known_value_remains_known_after_every_noiseless_repeat
    (n : ℕ) (latent : ℝ) :
    (Measure.dirac latent).map (readings n) = Measure.dirac (readings n latent) ∧
      ∀ i : Fin (n+1), readings n latent i = latent := by
  constructor
  · exact Measure.map_dirac (by unfold readings; fun_prop)
  · intro i; rfl

theorem actual_any_repeated_input_makes_the_noiseless_gram_determinant_zero
    {D ι : Type*} [Fintype ι] [DecidableEq ι]
    (kernel : D → D → ℝ) (input : ι → D) (i j : ι) (hij : i ≠ j)
    (hduplicate : input i = input j) :
    (fun a b : ι => kernel (input a) (input b) : Matrix ι ι ℝ).det = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext b
  rw [hduplicate]

theorem actual_noiseless_two_repeated_unit_prior_inputs_have_singular_gram :
    (!![1,1;1,1] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
  norm_num [Matrix.det_fin_two]

end SafeLearning.CompleteModulesGPNoiselessRepeats
