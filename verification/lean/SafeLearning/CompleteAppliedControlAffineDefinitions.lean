import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteAppliedControlAffineDefinitions

variable {n m : Type*} [Fintype n] [Fintype m]

def controlAffineField (drift : (n→ℝ)→n→ℝ)
    (inputMatrix : (n→ℝ)→Matrix n m ℝ) (state : n→ℝ) (input : m→ℝ) : n→ℝ :=
  drift state + (inputMatrix state).mulVec input

theorem actual_input_contribution_is_linear_at_every_fixed_state
    (drift : (n→ℝ)→n→ℝ) (inputMatrix : (n→ℝ)→Matrix n m ℝ)
    (state : n→ℝ) (first second : m→ℝ) (coefficient : ℝ) :
    controlAffineField drift inputMatrix state (first+second)=
      controlAffineField drift inputMatrix state first+
        controlAffineField drift inputMatrix state second-drift state ∧
    controlAffineField drift inputMatrix state (coefficient • first)-drift state=
      coefficient • (controlAffineField drift inputMatrix state first-drift state) := by
  constructor
  · simp only [controlAffineField,Matrix.mulVec_add]
    abel
  · simp only [controlAffineField,Matrix.mulVec_smul,add_sub_cancel_left]

def pendulumDrift (gravityOverLength damping : ℝ) (state : Fin 2→ℝ) : Fin 2→ℝ :=
  ![state 1,gravityOverLength*Real.sin (state 0)-damping*state 1]
def pendulumInputMatrix : Matrix (Fin 2) (Fin 1) ℝ := !![0;1]

theorem actual_pendulum_control_affine_velocity (gravityOverLength damping : ℝ)
    (state : Fin 2→ℝ) (input : Fin 1→ℝ) :
    controlAffineField (pendulumDrift gravityOverLength damping)
      (fun _=>pendulumInputMatrix) state input=
      ![state 1,gravityOverLength*Real.sin (state 0)-damping*state 1+input 0] := by
  ext i
  fin_cases i <;> simp [controlAffineField,pendulumDrift,pendulumInputMatrix,Matrix.mulVec,
    dotProduct,Fin.sum_univ_succ]

def unicycleInputMatrix (state : Fin 3→ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  !![Real.cos (state 2),0;Real.sin (state 2),0;0,1]

theorem actual_unicycle_control_affine_velocity (state : Fin 3→ℝ) (input : Fin 2→ℝ) :
    controlAffineField (fun _=>0) unicycleInputMatrix state input=
      ![input 0*Real.cos (state 2),input 0*Real.sin (state 2),input 1] := by
  ext i
  fin_cases i <;> simp [controlAffineField,unicycleInputMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_succ,mul_comm]

theorem actual_unicycle_input_matrix_depends_on_the_heading :
    unicycleInputMatrix ![0,0,0]≠unicycleInputMatrix ![0,0,Real.pi] := by
  intro h
  have he := congrArg (fun matrix=>matrix 0 0) h
  norm_num [unicycleInputMatrix] at he

def affineScalarInput (velocity : ℝ→ℝ) : Prop :=
  ∃offset gain:ℝ,∀input:ℝ,velocity input=offset+gain*input

theorem actual_squared_input_is_not_control_affine :
    ¬affineScalarInput (fun input:ℝ=>input^2) := by
  rintro ⟨offset,gain,h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num at h0 h1 h2
  linarith

theorem actual_sine_input_is_not_control_affine : ¬affineScalarInput Real.sin := by
  rintro ⟨offset,gain,h⟩
  have h0 := h 0
  have hpi := h Real.pi
  have hhalf := h (Real.pi/2)
  simp only [Real.sin_zero,mul_zero,add_zero] at h0
  have hoff : offset=0 := h0.symm
  simp only [Real.sin_pi,hoff,zero_add] at hpi
  have hgain : gain=0 := (mul_eq_zero.mp hpi.symm).resolve_right Real.pi_ne_zero
  simp only [Real.sin_pi_div_two,hoff,hgain,zero_mul,add_zero] at hhalf
  norm_num at hhalf

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- The derivative is an actual chain-rule consequence of the supplied state ODE,
with the input coefficient the composition of two actual continuous linear maps. -/
theorem actual_control_affine_chain_rule (certificate : E→ℝ) (trajectory : ℝ→E)
    (drift : E→E) (inputMap : E→U→L[ℝ]E) (input : ℝ→U)
    (gradient : E→L[ℝ]ℝ) (time : ℝ)
    (hcertificate : HasFDerivAt certificate gradient (trajectory time))
    (htrajectory : HasDerivAt trajectory
      (drift (trajectory time)+inputMap (trajectory time) (input time)) time) :
    HasDerivAt (certificate∘trajectory)
      (gradient (drift (trajectory time))+
        (gradient.comp (inputMap (trajectory time))) (input time)) time := by
  simpa only [map_add,ContinuousLinearMap.comp_apply] using
    hcertificate.comp_hasDerivAt time htrajectory

/-- A single affine derivative inequality is exactly an input half-space;
its convexity is derived, not a feasibility or optimizer premise. -/
theorem actual_derivative_requirement_is_a_convex_input_halfspace
    (gradient : E→L[ℝ]ℝ) (drift : E) (inputMap : U→L[ℝ]E) (threshold : ℝ) :
    {input:U | threshold≤gradient (drift+inputMap input)}=
      {input:U | threshold-gradient drift≤(gradient.comp inputMap) input} ∧
      Convex ℝ {input:U | threshold≤gradient (drift+inputMap input)} := by
  constructor
  · ext input
    simp only [Set.mem_setOf_eq,map_add,ContinuousLinearMap.comp_apply]
    constructor <;> intro h <;> linarith
  · intro first hf second hs a b ha hb hab
    simp only [Set.mem_setOf_eq,map_add,map_smul,ContinuousLinearMap.map_add] at *
    have hcomb := add_le_add (mul_le_mul_of_nonneg_left hf ha)
      (mul_le_mul_of_nonneg_left hs hb)
    simp only [smul_eq_mul] at *
    have hsum : a*threshold+b*threshold=threshold := by rw [←add_mul,hab,one_mul]
    have hconst : a*gradient drift+b*gradient drift=gradient drift := by
      rw [←add_mul,hab,one_mul]
    nlinarith

end SafeLearning.CompleteAppliedControlAffineDefinitions
