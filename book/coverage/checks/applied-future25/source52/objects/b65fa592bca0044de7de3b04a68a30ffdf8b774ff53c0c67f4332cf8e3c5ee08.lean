import SafeLearning.CompleteAppliedScalarODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteAppliedScalarStepResponse

def unitResponse (initial t : ℝ) : ℝ :=
  1/2+(initial-1/2)*Real.exp (-2*t)
def zeroResponse (t : ℝ) : ℝ := (1-Real.exp (-2*t))/2
def sourceTransfer (s : ℂ) : ℂ := 1/(s+2)

theorem actual_unit_input_trajectory_initial_and_ODE (initial t : ℝ) :
    unitResponse initial 0=initial ∧
    HasDerivAt (unitResponse initial) (-2*unitResponse initial t+1) t := by
  constructor
  · simp [unitResponse]
  · unfold unitResponse
    convert ((((hasDerivAt_id t).const_mul (-2)).exp).const_mul (initial-1/2)).const_add (1/2) using 1 <;>
      (try ext s) <;> simp only [id_eq] <;> ring

theorem actual_every_existing_unit_input_trajectory_has_this_formula
    (x : ℝ → ℝ) (initial horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0=initial)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (-2*x t+1) t) :
    ∀ t ∈ Icc 0 horizon,x t=unitResponse initial t := by
  have hec : ContinuousOn (fun t => x t-1/2) (Icc 0 horizon) :=
    hc.sub continuousOn_const
  have hei : x 0-1/2=initial-1/2 := by rw [hi]
  have hed : ∀ t ∈ Ico 0 horizon,
      HasDerivAt (fun s => x s-1/2) (-2*(x t-1/2)) t := by
    intro t ht
    convert (hd t ht).sub_const (1/2) using 1 <;> ring
  have hu := CompleteAppliedScalarODE.actual_linear_ODE_unique
    (fun t => x t-1/2) (-2) (initial-1/2) horizon hec hei hed
  intro t ht
  have h := hu t ht
  dsimp [CompleteAppliedScalarODE.solution] at h
  dsimp [unitResponse]
  linarith

theorem actual_source_zero_initial_response_and_DC_gain :
    (∀ t : ℝ,unitResponse 0 t=zeroResponse t) ∧
    zeroResponse 0=0 ∧ sourceTransfer 0=1/2 ∧
    Tendsto zeroResponse atTop (𝓝 (1/2:ℝ)) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t;dsimp [unitResponse,zeroResponse];ring
  · norm_num [zeroResponse]
  · norm_num [sourceTransfer]
  · have h := CompleteAppliedScalarODE.actual_linear_all_initial_attraction_iff (-2)
    have he := h.mpr (by norm_num) 1
    change Tendsto (fun t : ℝ => 1*Real.exp (-2*t)) atTop (𝓝 0) at he
    simp only [one_mul] at he
    change Tendsto (fun t : ℝ => (1-Real.exp (-2*t))/2) atTop (𝓝 (1/2:ℝ))
    simpa using
      ((tendsto_const_nhds (x := (1:ℝ))).sub he).div_const (2:ℝ)

theorem actual_all_initial_unit_responses_have_the_same_steady_output (initial : ℝ) :
    Tendsto (unitResponse initial) atTop (𝓝 (1/2:ℝ)) := by
  have he := (CompleteAppliedScalarODE.actual_linear_all_initial_attraction_iff (-2)).mpr
    (by norm_num) (initial-1/2)
  change Tendsto (fun t : ℝ => (initial-1/2)*Real.exp (-2*t)) atTop (𝓝 0) at he
  change Tendsto (fun t : ℝ => 1/2+(initial-1/2)*Real.exp (-2*t)) atTop (𝓝 (1/2:ℝ))
  simpa using (tendsto_const_nhds (x := (1/2:ℝ))).add he

theorem actual_nonzero_initial_state_adds_its_own_transient (initial t : ℝ) :
    unitResponse initial t=zeroResponse t+initial*Real.exp (-2*t) := by
  dsimp [unitResponse,zeroResponse]
  ring

theorem actual_arbitrary_input_zero_initial_response_superposition
    (u y : ℝ → ℝ) (initial t : ℝ)
    (hy : HasDerivAt y (-2*y t+u t) t) :
    HasDerivAt (fun s => y s+initial*Real.exp (-2*s))
      (-2*(y t+initial*Real.exp (-2*t))+u t) t := by
  have hz := CompleteAppliedScalarODE.actual_linear_solution_ODE (-2) initial t
  change HasDerivAt (fun s => initial*Real.exp (-2*s))
    (-2*(initial*Real.exp (-2*t))) t at hz
  convert hy.add hz using 1 <;> ring

theorem actual_arbitrary_input_initial_state_in_this_superposition
    (y : ℝ → ℝ) (initial : ℝ) (hy : y 0=0) :
    (y 0+initial*Real.exp (-2*0))=initial := by simp [hy]

theorem actual_source_algebraic_frequency_equation (s x u : ℂ) (hs : s+2≠0)
    (h : (s+2)*x=u) : x=sourceTransfer s*u := by
  dsimp [sourceTransfer]
  apply (mul_left_cancel₀ hs)
  rw [h]
  field_simp

end SafeLearning.CompleteAppliedScalarStepResponse
