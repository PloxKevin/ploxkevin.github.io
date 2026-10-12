import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open scoped Topology
namespace SafeLearning.CompleteAppliedImpulseResponse

def impulse (n : ℕ) : ℝ := if n = 0 then 0 else (1/2)^(n-1)
def unitImpulse (n : ℕ) : ℝ := if n = 0 then 1 else 0
def response (u : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (1/2)*response u n+u n

theorem actual_impulse_initial_and_recurrence :
    impulse 0 = 0 ∧ ∀ n, impulse (n+1)=(1/2)*impulse n+unitImpulse n := by
  constructor
  · simp [impulse]
  · intro n
    cases n with
    | zero => norm_num [impulse,unitImpulse]
    | succ n => simp [impulse,unitImpulse,pow_succ];ring

theorem actual_every_zero_initial_response_is_the_recursive_response
    (u x : ℕ → ℝ) (hx : x 0=0)
    (hs : ∀ n,x (n+1)=(1/2)*x n+u n) : ∀ n,x n=response u n := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => rw [hs n,ih];rfl

theorem actual_unit_impulse_has_the_printed_impulse_response :
    ∀ n,response unitImpulse n=impulse n := by
  intro n
  symm
  exact actual_every_zero_initial_response_is_the_recursive_response unitImpulse impulse
    actual_impulse_initial_and_recurrence.1 actual_impulse_initial_and_recurrence.2 n

theorem actual_impulse_nonnegative (n : ℕ) : 0 ≤ impulse n := by
  unfold impulse
  split <;> positivity

theorem actual_impulse_absolute_series : HasSum (fun n => |impulse n|) 2 := by
  have hg : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2)
      (by norm_num : (1/2:ℝ)<1) using 1 <;> norm_num
  have ht : HasSum (fun n => |impulse (n+1)|) 2 := by
    simpa [impulse,abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤1/2) _)] using hg
  simpa [impulse] using HasSum.zero_add (f := fun n => |impulse n|) ht

theorem actual_impulse_square_series : HasSum (fun n => impulse n ^ 2) (4/3) := by
  have hg : HasSum (fun n : ℕ => (1/4:ℝ)^n) (4/3) := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/4)
      (by norm_num : (1/4:ℝ)<1) using 1 <;> norm_num
  have ht : HasSum (fun n => impulse (n+1)^2) (4/3) := by
    convert hg using 1
    ext n
    simp only [impulse,Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  simpa [impulse] using HasSum.zero_add (f := fun n => impulse n^2) ht

theorem actual_impulse_sequence_norms :
    (∑' n,|impulse n|)=2 ∧
    Real.sqrt (∑' n,impulse n^2)=2/Real.sqrt 3 ∧
    (11547005/10000000:ℝ)<Real.sqrt (∑' n,impulse n^2) ∧
    Real.sqrt (∑' n,impulse n^2)<11547015/10000000 := by
  have hs := actual_impulse_square_series.tsum_eq
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hp : 0<Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have he : Real.sqrt (4/3:ℝ)=2/Real.sqrt 3 := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0:ℝ)≤4/3) (by positivity)).2
    field_simp
    nlinarith
  have hn := Real.sqrt_nonneg (4/3:ℝ)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤4/3)
  refine ⟨actual_impulse_absolute_series.tsum_eq,?_,?_,?_⟩
  · rw [hs];exact he
  · rw [hs];nlinarith
  · rw [hs];nlinarith

theorem actual_response_is_the_finite_convolution (u : ℕ → ℝ) (n : ℕ) :
    response u n=∑ i ∈ Finset.range n,(1/2)^(n-1-i)*u i := by
  induction n with
  | zero => simp [response]
  | succ n ih =>
    rw [response,ih,Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel,Nat.sub_self,pow_zero,one_mul]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hei : n-i=n-1-i+1 := by have := Finset.mem_range.mp hi;omega
    rw [hei,pow_succ]
    ring

theorem actual_bounded_input_uniform_output_bound
    (u : ℕ → ℝ) (M : ℝ) (hM : 0≤M) (hu : ∀ n,|u n|≤M) :
    ∀ n,|response u n|≤2*M := by
  intro n
  induction n with
  | zero => simp [response];linarith
  | succ n ih =>
    calc
      |response u (n+1)|≤|(1/2)*response u n|+|u n| := by
        simpa [response] using abs_add_le ((1/2:ℝ)*response u n) (u n)
      _=(1/2)*|response u n|+|u n| := by rw [abs_mul];norm_num
      _≤2*M := by linarith [hu n]

theorem actual_constant_unit_input_response (n : ℕ) :
    response (fun _ => 1) n=2*(1-(1/2:ℝ)^n) := by
  induction n with
  | zero => simp [response]
  | succ n ih => rw [response,ih,pow_succ];ring

theorem actual_constant_unit_input_attains_the_gain_in_the_limit :
    Tendsto (fun n => response (fun _ => 1) n) atTop (𝓝 (2:ℝ)) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  simpa [actual_constant_unit_input_response] using
    ((tendsto_const_nhds (x := (1:ℝ))).sub h).const_mul 2

def boundsAllBoundedInputs (gain : ℝ) : Prop :=
  ∀ (u : ℕ → ℝ) (M : ℝ),0≤M → (∀ n,|u n|≤M) →
    ∀ n,|response u n|≤gain*M

theorem actual_induced_bounded_input_gain_is_exactly_two :
    IsLeast {gain : ℝ | boundsAllBoundedInputs gain} 2 := by
  constructor
  · exact actual_bounded_input_uniform_output_bound
  · intro gain hg
    have h : ∀ n,response (fun _ => 1) n≤gain := by
      intro n
      have he := hg (fun _ => 1) 1 (by norm_num) (by intro k;norm_num) n
      have hl := le_abs_self (response (fun _ => 1) n)
      norm_num at he
      linarith
    exact le_of_tendsto' actual_constant_unit_input_attains_the_gain_in_the_limit h

theorem actual_single_impulse_energy_norm_is_strictly_smaller_than_bounded_input_gain :
    Real.sqrt (∑' n,impulse n^2)<2 := by
  rw [actual_impulse_square_series.tsum_eq]
  have hn := Real.sqrt_nonneg (4/3:ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤4/3)
  nlinarith

end SafeLearning.CompleteAppliedImpulseResponse
