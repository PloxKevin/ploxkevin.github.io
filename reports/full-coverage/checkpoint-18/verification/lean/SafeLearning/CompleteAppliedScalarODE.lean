import SafeLearning.CompleteAppliedScalarTrajectories
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedScalarODE
open Set Filter
open scoped Topology

def solution (rate initial t : ℝ) : ℝ := initial*Real.exp (rate*t)

theorem actual_linear_solution_initial (rate initial : ℝ) : solution rate initial 0=initial := by
  simp [solution]

theorem actual_linear_solution_ODE (rate initial t : ℝ) :
    HasDerivAt (solution rate initial) (rate*solution rate initial t) t := by
  unfold solution
  convert (((hasDerivAt_id t).const_mul rate).exp).const_mul initial using 1 <;> (try ext s) <;> simp only [id_eq] <;> ring

theorem actual_linear_ODE_unique (x : ℝ → ℝ) (rate initial horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0=initial)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (rate*x t) t) :
    ∀ t ∈ Icc 0 horizon,x t=solution rate initial t := by
  let g : ℝ → ℝ := fun t => Real.exp (-rate*t)*x t
  have hgcont : ContinuousOn g (Icc 0 horizon) := by
    apply ContinuousOn.mul _ hc
    fun_prop
  have hgderiv : ∀ t ∈ Ico 0 horizon,HasDerivWithinAt g 0 (Ici t) t := by
    intro t ht
    have h : HasDerivAt g 0 t := by
      convert (((hasDerivAt_id t).const_mul (-rate)).exp).mul (hd t ht) using 1 <;> (try ext s) <;> simp only [id_eq,g,Pi.mul_apply] <;> ring
    exact h.hasDerivWithinAt
  have hg := constant_of_has_deriv_right_zero hgcont hgderiv
  intro t ht
  have he : Real.exp (-rate*t)*x t=initial := by simpa [g,hi] using hg t ht
  have hp : Real.exp (rate*t)*Real.exp (-rate*t)=1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have h := congrArg (fun z : ℝ => Real.exp (rate*t)*z) he
  rw [← mul_assoc,hp,one_mul] at h
  simpa [solution,mul_comm] using h

theorem actual_linear_all_initial_attraction_iff (rate : ℝ) :
    (∀ initial : ℝ,Tendsto (solution rate initial) atTop (𝓝 0)) ↔ rate<0 := by
  constructor
  · intro h
    have he : Tendsto (fun t : ℝ => Real.exp (rate*t)) atTop (𝓝 0) := by
      have h1 := h 1
      change Tendsto (fun t : ℝ => 1*Real.exp (rate*t)) atTop (𝓝 0) at h1
      simpa only [one_mul] using h1
    rw [Real.tendsto_exp_comp_nhds_zero] at he
    exact (tendsto_const_mul_atBot_iff_neg tendsto_id).mp he
  · intro hr initial
    have he := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hr)
    change Tendsto (fun t : ℝ => initial*Real.exp (rate*t)) atTop (𝓝 0)
    simpa only [mul_zero,Function.comp_def,id_eq] using he.const_mul initial

def lyapunovStable (rate : ℝ) : Prop :=
  ∀ epsilon : ℝ,0<epsilon → ∃ delta : ℝ,0<delta ∧
    ∀ initial : ℝ,|initial|<delta → ∀ t : ℝ,0≤t → |solution rate initial t|<epsilon

theorem actual_nonpositive_rate_is_stable (rate : ℝ) (hr : rate≤0) : lyapunovStable rate := by
  intro epsilon he
  refine ⟨epsilon,he,?_⟩
  intro initial hi t ht
  have hfac : Real.exp (rate*t)≤1 := by
    rw [← Real.exp_zero,Real.exp_le_exp]
    exact mul_nonpos_of_nonpos_of_nonneg hr ht
  rw [solution,abs_mul,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left hfac (abs_nonneg initial)).trans_lt (by simpa using hi)

theorem actual_positive_rate_grows (rate : ℝ) (hr : 0<rate) (initial : ℝ) (hi : 0 < initial) :
    Tendsto (solution rate initial) atTop atTop := by
  have he := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hr)
  change Tendsto (fun t : ℝ => initial*Real.exp (rate*t)) atTop atTop
  exact he.const_mul_atTop hi

theorem actual_positive_rate_is_unstable (rate : ℝ) (hr : 0<rate) : ¬lyapunovStable rate := by
  intro h
  obtain ⟨delta,hd,hall⟩ := h 1 (by norm_num)
  let initial : ℝ := delta/2
  have hi : 0 < initial := by dsimp [initial];linarith
  have hsmall : |initial|<delta := by rw [abs_of_pos hi];dsimp [initial];linarith
  have hg := actual_positive_rate_grows rate hr initial hi
  obtain ⟨t,ht,hlarge⟩ := ((eventually_ge_atTop (0:ℝ)).and
    (hg.eventually (eventually_ge_atTop (1:ℝ)))).exists
  have hs := hall initial hsmall t ht
  have hpos : 0<solution rate initial t := mul_pos hi (Real.exp_pos _)
  rw [abs_of_pos hpos] at hs
  linarith

theorem actual_stability_iff_nonpositive_rate (rate : ℝ) : lyapunovStable rate ↔ rate≤0 := by
  constructor
  · intro h
    by_contra hn
    exact actual_positive_rate_is_unstable rate (lt_of_not_ge hn) h
  · exact actual_nonpositive_rate_is_stable rate

theorem actual_feedback_linear_plant (k x : ℝ) : 2*x-k*x=(2-k)*x := by ring

theorem actual_feedback_stability_and_attraction (k : ℝ) :
    ((lyapunovStable (2-k) ∧ ∀ initial : ℝ,Tendsto (solution (2-k) initial) atTop (𝓝 0))
      ↔ 2<k) ∧
    (k=2 → lyapunovStable (2-k) ∧ (∀ initial t : ℝ,solution (2-k) initial t=initial) ∧
      ¬(∀ initial : ℝ,Tendsto (solution (2-k) initial) atTop (𝓝 0))) ∧
    (k<2 → ¬lyapunovStable (2-k) ∧
      ∀ initial : ℝ,0 < initial → Tendsto (solution (2-k) initial) atTop atTop) := by
  constructor
  · rw [actual_stability_iff_nonpositive_rate,actual_linear_all_initial_attraction_iff]
    constructor <;> intro h <;> (try constructor) <;> linarith
  constructor
  · intro hk
    subst k
    refine ⟨actual_nonpositive_rate_is_stable (2-2) (by norm_num),?_,?_⟩
    · intro initial t;simp [solution]
    · rw [actual_linear_all_initial_attraction_iff];norm_num
  · intro hk
    exact ⟨actual_positive_rate_is_unstable (2-k) (by linarith),
      fun initial hi => actual_positive_rate_grows (2-k) (by linarith) initial hi⟩

theorem actual_quadratic_certificate_derivative (x : ℝ → ℝ) (t : ℝ)
    (hx : HasDerivAt x (-2*x t) t) :
    HasDerivAt (fun s => x s^2) (-4*(x t)^2) t := by
  convert hx.pow 2 using 1 <;> ring

theorem actual_quadratic_certificate_solution (initial t : ℝ) :
    (solution (-2) initial t)^2=initial^2*Real.exp (-4*t) ∧
    |solution (-2) initial t|=|initial| *Real.exp (-2*t) := by
  constructor
  · rw [solution,mul_pow,← Real.exp_nat_mul]
    congr 2
    ring
  · rw [solution,abs_mul,abs_of_pos (Real.exp_pos _)]

theorem actual_quadratic_ODE_certificate (x : ℝ → ℝ) (initial horizon : ℝ)
    (hc : ContinuousOn x (Icc 0 horizon)) (hi : x 0=initial)
    (hd : ∀ t ∈ Ico 0 horizon,HasDerivAt x (-2*x t) t) :
    ∀ t ∈ Icc 0 horizon,x t^2=initial^2*Real.exp (-4*t) ∧
      |x t|=|initial| *Real.exp (-2*t) := by
  have h := actual_linear_ODE_unique x (-2) initial horizon hc hi hd
  intro t ht
  rw [h t ht]
  exact actual_quadratic_certificate_solution initial t

end SafeLearning.CompleteAppliedScalarODE
