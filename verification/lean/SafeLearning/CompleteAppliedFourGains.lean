import SafeLearning.CompleteAppliedCircleFrequency
import SafeLearning.CompleteModulesDissipation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace SafeLearning.CompleteAppliedFourGains
open CompleteAppliedCircleFrequency CompleteModulesDissipation

def actualState (input : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => (4/5)*actualState input n+input n
def actualOutput (input : ℕ → ℝ) (n : ℕ) : ℝ := (3/5)*actualState input n
def impulseInput (n : ℕ) : ℝ := if n=0 then 1 else 0
def impulseResponse : ℕ → ℝ
  | 0 => 0
  | n+1 => (3/5)*(4/5:ℝ)^n
def actualStorage (state : ℝ) : ℝ := (9/5)*state^2
def actualGramian : ℝ := ∑' n : ℕ, (4/5:ℝ)^(2*n)

theorem actual_every_source_recurrence_is_the_constructed_zero_state
    (input state : ℕ → ℝ) (hzero : state 0=0)
    (hnext : ∀ n, state (n+1)=(4/5)*state n+input n) :
    ∀ n, state n=actualState input n := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih => rw [hnext,ih,actualState]

theorem actual_impulse_has_the_literal_state_and_output :
    (∀ n : ℕ, actualState impulseInput (n+1)=(4/5:ℝ)^n) ∧
      actualOutput impulseInput=impulseResponse := by
  have hs (n : ℕ) : actualState impulseInput (n+1)=(4/5:ℝ)^n := by
    induction n with
    | zero => norm_num [actualState,impulseInput]
    | succ n ih =>
      rw [actualState,ih]
      simp [impulseInput,pow_succ]
      ring
  refine ⟨hs,?_⟩
  ext n
  cases n with
  | zero => simp [actualOutput,actualState,impulseResponse]
  | succ n => simp [actualOutput,hs,impulseResponse]

theorem actual_impulse_absolute_sum_is_three :
    HasSum (fun n => |impulseResponse n|) (3:ℝ) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤4/5)
    (by norm_num : (4/5:ℝ)<1)).mul_left (3/5:ℝ)
  have hs : HasSum (fun n => |impulseResponse (n+1)|) (3:ℝ) := by
    convert h using 1
    · ext n
      rw [impulseResponse,abs_of_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by norm_num) n))]
    · norm_num
  have hh := (hasSum_nat_add_iff (f:=fun n => |impulseResponse n|) (g:=(3:ℝ)) 1).mp hs
  simpa [impulseResponse] using hh

theorem actual_impulse_square_sum_is_one :
    HasSum (fun n => (impulseResponse n)^2) (1:ℝ) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤16/25)
    (by norm_num : (16/25:ℝ)<1)).mul_left (9/25:ℝ)
  have hs : HasSum (fun n => (impulseResponse (n+1))^2) (1:ℝ) := by
    convert h using 1
    · ext n
      simp only [impulseResponse,mul_pow]
      rw [←pow_mul, Nat.mul_comm n 2, pow_mul]
      norm_num
    · norm_num
  have hh := (hasSum_nat_add_iff (f:=fun n => (impulseResponse n)^2) (g:=(1:ℝ)) 1).mp hs
  simpa [impulseResponse] using hh

theorem actual_impulse_norms_are_three_and_one :
    (∑' n, |impulseResponse n|)=3 ∧
      Real.sqrt (∑' n, (impulseResponse n)^2)=1 := by
  rw [actual_impulse_absolute_sum_is_three.tsum_eq,actual_impulse_square_sum_is_one.tsum_eq]
  norm_num

theorem actual_source_resolvent_is_the_printed_transfer (z : ℂ) :
    (3/5:ℂ)*(z-4/5)⁻¹=sourceTransfer z := by
  simp [sourceTransfer,div_eq_mul_inv]

theorem actual_true_controllability_gramian_and_storage_check :
    actualGramian=25/9 ∧ actualGramian=(16/25)*actualGramian+1 ∧
      (9/25)*actualGramian=1 ∧
      |actualGramian-(1389/500:ℝ)|<1/2000 ∧
      actualGramian≠(1389/500:ℝ) ∧ (9/25:ℝ)*(1389/500)=12501/12500 := by
  have h := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤16/25)
    (by norm_num : (16/25:ℝ)<1)
  have he : actualGramian=25/9 := by
    unfold actualGramian
    have hf : (fun n : ℕ => (4/5:ℝ)^(2*n))=(fun n : ℕ => (16/25:ℝ)^n) := by
      ext n
      rw [pow_mul]
      norm_num
    rw [hf,h.tsum_eq]
    norm_num
  rw [he]
  norm_num

theorem actual_storage_has_the_literal_negative_square_identity (state input : ℝ) :
    actualStorage ((4/5)*state+input)-actualStorage state-9*input^2+((3/5)*state)^2=
      -(36/125)*(state-5*input)^2 := by
  simp only [actualStorage]
  ring

theorem actual_every_step_has_the_source_storage_dissipation (state input : ℝ) :
    actualStorage ((4/5)*state+input)-actualStorage state ≤
      9*input^2-((3/5)*state)^2 := by
  have h := actual_storage_has_the_literal_negative_square_identity state input
  nlinarith [sq_nonneg (state-5*input)]

theorem actual_every_input_has_the_finite_horizon_energy_bound
    (input : ℕ → ℝ) (horizon : ℕ) :
    (∑ n ∈ Finset.range horizon, (actualOutput input n)^2) ≤
      9*(∑ n ∈ Finset.range horizon, (input n)^2) := by
  have h := actual_nonnegative_storage_implies_finite_energy_gain
    (fun n => actualStorage (actualState input n)) input (actualOutput input) 3
    (fun n => by dsimp [actualStorage]; positivity)
    (fun n => by simpa [actualState,actualOutput,show (3:ℝ)^2=9 by norm_num] using
      actual_every_step_has_the_source_storage_dissipation (actualState input n) (input n)) horizon
  simpa [actualState,actualStorage,show (3:ℝ)^2=9 by norm_num] using h

theorem actual_every_square_summable_input_has_a_square_summable_output_with_gain_three
    (input : ℕ → ℝ) (hinput : Summable (fun n => (input n)^2)) :
    Summable (fun n => (actualOutput input n)^2) ∧
      (∑' n, (actualOutput input n)^2) ≤ 9*(∑' n, (input n)^2) := by
  have h := actual_storage_dissipation_with_square_summable_input_has_bounded_square_summable_output
    (fun n => actualStorage (actualState input n)) input (actualOutput input) 3
    (fun n => by dsimp [actualStorage]; positivity)
    (fun n => by simpa [actualState,actualOutput,show (3:ℝ)^2=9 by norm_num] using
      actual_every_step_has_the_source_storage_dissipation (actualState input n) (input n)) hinput
  simpa [actualState,actualStorage,show (3:ℝ)^2=9 by norm_num] using h

theorem actual_every_square_summable_input_has_the_norm_bound
    (input : ℕ → ℝ) (hinput : Summable (fun n => (input n)^2)) :
    Real.sqrt (∑' n, (actualOutput input n)^2) ≤
      3*Real.sqrt (∑' n, (input n)^2) := by
  have h := Real.sqrt_le_sqrt
    (actual_every_square_summable_input_has_a_square_summable_output_with_gain_three input hinput).2
  rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤9)] at h
  norm_num at h
  exact h

end SafeLearning.CompleteAppliedFourGains
