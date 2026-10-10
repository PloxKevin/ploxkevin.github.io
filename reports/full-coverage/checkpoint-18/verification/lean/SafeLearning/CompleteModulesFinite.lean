import SafeLearning.Modules
import SafeLearning.BookApplications

set_option autoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesFinite

-- The discrete enclosure graph: index i represents temperature 52+2i.
def thermalActionAllowed (i : ℕ) (run : Bool) : Prop :=
  run=true ∨ (run=false ∧ 2 ≤ i ∧ i < 4)

instance (i : ℕ) (run : Bool) : Decidable (thermalActionAllowed i run) := by
  unfold thermalActionAllowed
  infer_instance

def thermalSuccessor (i : ℕ) (run : Bool) : ℕ := if run then i+1 else i-2

def thermalPredecessor (cap : ℕ) (S : Set ℕ) : Set ℕ :=
  {i | i ≤ cap ∧ ∃ run, thermalActionAllowed i run ∧ thermalSuccessor i run ∈ S}

theorem thermal_kernel_controlled_invariant :
    ∀ i ∈ Iic 3, ∃ run, thermalActionAllowed i run ∧ thermalSuccessor i run ∈ Iic 3 := by
  intro i hi
  simp only [mem_Iic] at hi ⊢
  by_cases h : i < 3
  · refine ⟨true,Or.inl rfl,?_⟩
    simp only [thermalSuccessor,Bool.true_eq,ite_true]
    omega
  · refine ⟨false,Or.inr ⟨rfl,by omega,by omega⟩,?_⟩
    simp only [thermalSuccessor,Bool.false_eq_true,ite_false]
    omega

theorem thermal_predecessor_cap60 : thermalPredecessor 4 (Iic 4)=Iic 3 := by
  ext i
  simp only [thermalPredecessor,mem_setOf_eq,mem_Iic]
  constructor
  · rintro ⟨hi,run,ha,hs⟩
    cases run <;> simp_all [thermalActionAllowed,thermalSuccessor] <;> omega
  · intro hi
    obtain ⟨run,ha,hs⟩ := thermal_kernel_controlled_invariant i hi
    exact ⟨by omega,run,ha,by simpa using le_trans hs (by norm_num : 3 ≤ 4)⟩

theorem thermal_predecessor_fixed : thermalPredecessor 4 (Iic 3)=Iic 3 := by
  ext i
  simp only [thermalPredecessor,mem_setOf_eq,mem_Iic]
  constructor
  · rintro ⟨hi,run,ha,hs⟩
    cases run <;> simp_all [thermalActionAllowed,thermalSuccessor] <;> omega
  · intro hi
    obtain ⟨run,ha,hs⟩ := thermal_kernel_controlled_invariant i hi
    exact ⟨by omega,run,ha,hs⟩

theorem thermal_predecessor_cap62 : thermalPredecessor 5 (Iic 5)=Iic 4 := by
  ext i
  simp only [thermalPredecessor,mem_setOf_eq,mem_Iic]
  constructor
  · rintro ⟨hi,run,ha,hs⟩
    cases run <;> simp_all [thermalActionAllowed,thermalSuccessor] <;> omega
  · intro hi
    refine ⟨by omega,true,Or.inl rfl,?_⟩
    simp [thermalSuccessor]
    omega

theorem thermal_predecessor_cap62_second : thermalPredecessor 5 (Iic 4)=Iic 3 := by
  ext i
  simp only [thermalPredecessor,mem_setOf_eq,mem_Iic]
  constructor
  · rintro ⟨hi,run,ha,hs⟩
    cases run <;> simp_all [thermalActionAllowed,thermalSuccessor] <;> omega
  · intro hi
    obtain ⟨run,ha,hs⟩ := thermal_kernel_controlled_invariant i hi
    exact ⟨by omega,run,ha,by simpa using le_trans hs (by norm_num : 3 ≤ 4)⟩

theorem thermal_predecessor_cap62_fixed : thermalPredecessor 5 (Iic 3)=Iic 3 := by
  ext i
  simp only [thermalPredecessor,mem_setOf_eq,mem_Iic]
  constructor
  · rintro ⟨hi,run,ha,hs⟩
    cases run <;> simp_all [thermalActionAllowed,thermalSuccessor] <;> omega
  · intro hi
    obtain ⟨run,ha,hs⟩ := thermal_kernel_controlled_invariant i hi
    exact ⟨by omega,run,ha,hs⟩

theorem thermal_kernel_maximal (S : Set ℕ) (hbound : S ⊆ Iic 5)
    (hinv : ∀ i ∈ S, ∃ run, thermalActionAllowed i run ∧ thermalSuccessor i run ∈ S) :
    S ⊆ Iic 3 := by
  intro i hi
  have hi5 := hbound hi
  obtain ⟨run,ha,hs⟩ := hinv i hi
  by_cases h3 : i ≤ 3
  · exact h3
  · have hrun : run=true := by
      cases run <;> simp_all [thermalActionAllowed] <;> omega
    subst run
    have hs' : i+1 ∈ S := by simpa [thermalSuccessor] using hs
    have hs5 := hbound hs'
    obtain ⟨run',ha',hsnext⟩ := hinv (i+1) hs'
    have hsnext5 := hbound hsnext
    cases run' <;> simp_all [thermalActionAllowed,thermalSuccessor,mem_Iic] <;> omega

theorem thermal_infinite_trajectory_exists (i : ℕ) (hi : i ≤ 3) :
    ∃ state : ℕ → ℕ, ∃ action : ℕ → Bool,
      state 0=i ∧ ∀ n, state n ≤ 3 ∧ thermalActionAllowed (state n) (action n) ∧
        state (n+1)=thermalSuccessor (state n) (action n) := by
  classical
  let policy (x : {j : ℕ // j ≤ 3}) : Bool :=
    Classical.choose (thermal_kernel_controlled_invariant x.1 x.2)
  have hp (x : {j : ℕ // j ≤ 3}) :
      thermalActionAllowed x.1 (policy x) ∧ thermalSuccessor x.1 (policy x) ≤ 3 :=
    Classical.choose_spec (thermal_kernel_controlled_invariant x.1 x.2)
  let step (x : {j : ℕ // j ≤ 3}) : {j : ℕ // j ≤ 3} :=
    ⟨thermalSuccessor x.1 (policy x),(hp x).2⟩
  let state (n : ℕ) : {j : ℕ // j ≤ 3} := (step^[n]) ⟨i,hi⟩
  refine ⟨fun n => (state n).1,fun n => policy (state n),?_,?_⟩
  · rfl
  · intro n
    refine ⟨(state n).2,(hp (state n)).1,?_⟩
    change ((step^[n+1]) ⟨i,hi⟩).1=thermalSuccessor (state n).1 (policy (state n))
    rw [Function.iterate_succ_apply']

theorem thermal_infinite_trajectory_necessary (state : ℕ → ℕ) (action : ℕ → Bool)
    (hbound : ∀ n, state n ≤ 5)
    (hallowed : ∀ n, thermalActionAllowed (state n) (action n))
    (hstep : ∀ n, state (n+1)=thermalSuccessor (state n) (action n)) : state 0 ≤ 3 := by
  have h₀ := hbound 0
  have h₁ := hbound 1
  have h₂ := hbound 2
  have ha₀ := hallowed 0
  have ha₁ := hallowed 1
  have hs₀ := hstep 0
  have hs₁ := hstep 1
  by_contra h
  have hr₀ : action 0=true := by
    cases hx : action 0 <;> simp_all [thermalActionAllowed] <;> omega
  have hs₀' : state 1=state 0+1 := by simpa [thermalSuccessor,hr₀] using hs₀
  have hr₁ : action 1=true := by
    cases hx : action 1 <;> simp_all [thermalActionAllowed] <;> omega
  have hs₁' : state 2=state 1+1 := by simpa [thermalSuccessor,hr₁] using hs₁
  omega

theorem thermal_infinite_viability_iff (i : ℕ) :
    (∃ state : ℕ → ℕ, ∃ action : ℕ → Bool, state 0=i ∧
      ∀ n, state n ≤ 5 ∧ thermalActionAllowed (state n) (action n) ∧
        state (n+1)=thermalSuccessor (state n) (action n)) ↔ i ≤ 3 := by
  constructor
  · rintro ⟨state,action,hzero,hall⟩
    rw [← hzero]
    exact thermal_infinite_trajectory_necessary state action
      (fun n => (hall n).1) (fun n => (hall n).2.1) (fun n => (hall n).2.2)
  · intro hi
    obtain ⟨state,action,hzero,hall⟩ := thermal_infinite_trajectory_exists i hi
    refine ⟨state,action,hzero,fun n => ?_⟩
    exact ⟨le_trans (hall n).1 (by norm_num),(hall n).2⟩

theorem thermal_viable_action_count :
    (Finset.univ.filter (fun run : Bool => thermalActionAllowed 0 run ∧ thermalSuccessor 0 run ≤ 3)).card=1 ∧
    (Finset.univ.filter (fun run : Bool => thermalActionAllowed 1 run ∧ thermalSuccessor 1 run ≤ 3)).card=1 ∧
    (Finset.univ.filter (fun run : Bool => thermalActionAllowed 2 run ∧ thermalSuccessor 2 run ≤ 3)).card=2 ∧
    (Finset.univ.filter (fun run : Bool => thermalActionAllowed 3 run ∧ thermalSuccessor 3 run ≤ 3)).card=1 := by
  decide

-- General finite-horizon Bellman verification for discounted controlled graphs.
theorem discounted_bellman_upper {X U : Type*} (state : ℕ → X) (action : ℕ → U)
    (transition : X → U → X) (reward : X → U → ℝ) (V : X → ℝ)
    (gamma : ℝ) (hg : 0 ≤ gamma)
    (hdynamics : ∀ n, state (n+1)=transition (state n) (action n))
    (hbellman : ∀ n, reward (state n) (action n)+gamma*V (transition (state n) (action n)) ≤ V (state n)) :
    ∀ n, (∑ k ∈ Finset.range n, gamma^k*reward (state k) (action k))+
      gamma^n*V (state n) ≤ V (state 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := hbellman n
    rw [← hdynamics n] at hstep
    have hm := mul_le_mul_of_nonneg_left hstep (pow_nonneg hg n)
    rw [Finset.sum_range_succ,pow_succ]
    nlinarith

-- Elementary exact exercises and counterexamples, with universal conclusions.
theorem landscape_safe_set (x : ℝ) : 0 ≤ 4-x^2 ↔ x ∈ Icc (-2) 2 := by
  constructor
  · intro h; constructor <;> nlinarith [sq_nonneg (x-2),sq_nonneg (x+2)]
  · intro h; nlinarith [mul_nonneg (by linarith [h.1] : 0 ≤ x+2) (by linarith [h.2] : 0 ≤ 2-x)]

theorem viability_negation {U T : Type*} (failure : U → T → Prop) :
    (¬ ∃ u, ∀ t, ¬ failure u t) ↔ ∀ u, ∃ t, failure u t := by
  classical
  simp only [not_exists,not_forall,not_not]

theorem some_failure_compatible_with_viability :
    (∃ u : Bool, ∀ _t : ℕ, ¬ (u=true)) ∧ (∃ u : Bool, ∃ _t : ℕ, u=true) := by
  exact ⟨⟨false,by simp⟩,⟨true,0,rfl⟩⟩

theorem robust_half_radius_iff (r : ℝ) (hr : 0 ≤ r) :
    (∀ x w : ℝ, |x| ≤ r → |w| ≤ 1/10 → |(1/2)*x+w| ≤ r) ↔ 1/5 ≤ r := by
  constructor
  · intro h
    have hb := h r (1/10) (by simp [abs_of_nonneg hr]) (by norm_num)
    have hb' := (abs_le.mp hb).2
    linarith
  · intro h x w hx hw
    calc |(1/2)*x+w| ≤ |(1/2)*x|+|w| := abs_add_le _ _
      _ = (1/2)*|x|+|w| := by rw [abs_mul]; norm_num
      _ ≤ r := by linarith

theorem first_drift_violation (n : ℕ) : (n:ℝ)/100 ≤ 1 ↔ n ≤ 100 := by
  constructor
  · intro h; have hn : (n:ℝ) ≤ 100 := by linarith
    exact_mod_cast hn
  · intro h
    have hn : (n:ℝ) ≤ 100 := by exact_mod_cast h
    linarith

theorem kkt_scalar_minimum (x : ℝ) (hx : x ≤ 1) :
    1 ≤ (x-2)^2 ∧ ((x-2)^2=1 ↔ x=1) := by
  constructor
  · nlinarith [sq_nonneg (x-1)]
  · constructor
    · intro h; nlinarith
    · intro h; rw [h]; norm_num

theorem schur_scalar_psd_iff (t : ℝ) :
    (∀ x y : ℝ, 0 ≤ t*x^2+4*x*y+y^2) ↔ 4 ≤ t := by
  constructor
  · intro h; have h' := h 1 (-2); nlinarith
  · intro h x y
    have hi : t*x^2+4*x*y+y^2=(t-4)*x^2+(y+2*x)^2 := by ring
    rw [hi]
    positivity

theorem scalar_lyapunov_iff (a p : ℝ) (hp : 0 < p) :
    a^2*p-p < 0 ↔ |a| < 1 := by
  rw [abs_lt]
  constructor
  · intro h
    have ha : a^2 < 1 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (a-1),sq_nonneg (a+1)]
  · intro h
    have ha : a^2 < 1 := by nlinarith [mul_pos (by linarith [h.1] : 0 < a+1) (by linarith [h.2] : 0 < 1-a)]
    nlinarith

theorem singular_psd_range_condition (b c : ℝ) :
    (∀ x y : ℝ, 0 ≤ 2*b*x*y+c*y^2) ↔ b=0 ∧ 0 ≤ c := by
  constructor
  · intro h
    have hc := h 0 1
    have hb := h (-(c+1)/(2*b)) 1
    constructor
    · by_contra hn
      have hi : 2*b*(-(c+1)/(2*b))*1+c*1^2= -1 := by field_simp; ring
      rw [hi] at hb
      norm_num at hb
    · nlinarith
  · rintro ⟨rfl,hc⟩ x y; simp; positivity

theorem s_procedure_interval (x : ℝ) (hx : |x| ≤ 1) : x ≤ 1 := by
  exact (abs_le.mp hx).2

theorem s_procedure_identity (x : ℝ) : x-1+(1/2)*(1-x^2)= -(x-1)^2/2 := by ring

theorem neuron_interval_exact (x y : ℝ) (hx : x ∈ Icc 1 2) (hy : y ∈ Icc (-1) 1) :
    2*x-3*y+1 ∈ Icc 0 8 ∧ max (2*x-3*y+1) 0 ∈ Icc 0 8 := by
  have hb : 2*x-3*y+1 ∈ Icc (0:ℝ) 8 := by
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  exact ⟨hb,by rwa [max_eq_left hb.1]⟩

theorem unstable_relu_triangle (z : ℝ) (hz : z ∈ Icc (-2) 3) :
    (2/5)*z ≤ max z 0 ∧ max z 0 ≤ (3/5)*(z+2) := by
  by_cases hp : 0 ≤ z
  · rw [max_eq_left hp]; constructor <;> linarith [hz.2]
  · rw [max_eq_right (le_of_not_ge hp)]; constructor <;> linarith [hz.1]

theorem crown_negative_output (z : ℝ) (hz : z ∈ Icc (-1) 2) :
    1-(4/3)*(z+1) ≤ 1-2*max z 0 ∧ 1-2*max z 0 ≤ 1 := by
  constructor
  · by_cases hp : 0 ≤ z
    · rw [max_eq_left hp]; linarith [hz.2]
    · rw [max_eq_right (le_of_not_ge hp)]; linarith [hz.1]
  · linarith [le_max_right z 0]

theorem affine_l2_ball (dx dy : ℝ) (h : dx^2+dy^2 ≤ (1/5)^2) :
    |3*dx-4*dy| ≤ 1 := by
  have hc : (3*dx-4*dy)^2+(4*dx+3*dy)^2=25*(dx^2+dy^2) := by ring
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (4*dx+3*dy),sq_nonneg (3*dx-4*dy+1),sq_nonneg (3*dx-4*dy-1)]

theorem affine_infinity_ball (dx dy : ℝ) (hx : |dx| ≤ 1/5) (hy : |dy| ≤ 1/5) :
    |3*dx-4*dy| ≤ 7/5 := by
  have hx' := abs_le.mp hx; have hy' := abs_le.mp hy
  rw [abs_le]; constructor <;> linarith [hx'.1,hx'.2,hy'.1,hy'.2]

theorem affine_minima_attained :
    (3*(-3/25:ℝ)-4*(4/25)= -1) ∧
    ((-3/25:ℝ)^2+(4/25)^2=(1/5)^2) ∧
    (3*(-1/5:ℝ)-4*(1/5)= -7/5) := by norm_num

end SafeLearning.CompleteModulesFinite
