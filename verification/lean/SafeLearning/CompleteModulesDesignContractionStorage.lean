import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 10000
noncomputable section
open scoped BigOperators
namespace SafeLearning.CompleteModulesDesignContractionStorage

def sourceBound (n : ℕ) : ℝ := 3*(4/5:ℝ)^n
def sourceLogCutoff : ℝ := Real.log (1/30)/Real.log (4/5)

theorem actual_source_tolerance_is_equivalent_to_the_actual_log_cutoff (n : ℕ) :
    sourceBound n≤1/10 ↔ sourceLogCutoff≤(n:ℝ) := by
  have hq : Real.log (4/5:ℝ)<0 := Real.log_neg (by norm_num) (by norm_num)
  rw [sourceBound,sourceLogCutoff,div_le_iff_of_neg hq,
    ←Real.log_le_log_iff (by positivity : (0:ℝ)<3*(4/5)^n) (by norm_num)]
  rw [Real.log_mul (by norm_num : (3:ℝ)≠0) (pow_ne_zero n (by norm_num)),Real.log_pow]
  have hd : Real.log (1/30:ℝ)=Real.log (1/10:ℝ)-Real.log 3 := by
    rw [←Real.log_div (by norm_num : (1/10:ℝ)≠0) (by norm_num : (3:ℝ)≠0)]
    norm_num
  rw [hd]
  constructor <;>intro h <;>linarith

theorem actual_source_first_integer_tolerance_is_sixteen :
    (1/10:ℝ)<sourceBound 15 ∧ sourceBound 16≤1/10 ∧
      ∀ n,sourceBound n≤1/10 ↔ 16≤n := by
  refine ⟨by norm_num [sourceBound],by norm_num [sourceBound],?_⟩
  intro n
  constructor
  · intro h
    by_contra hn
    have hsmall : n≤15 := by omega
    have hp : (4/5:ℝ)^15≤(4/5:ℝ)^n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hsmall
    have h15 : (1/10:ℝ)<sourceBound 15 := by norm_num [sourceBound]
    unfold sourceBound at *
    linarith
  · intro hn
    have hp : (4/5:ℝ)^n≤(4/5:ℝ)^16 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have h16 : sourceBound 16≤1/10 := by norm_num [sourceBound]
    unfold sourceBound at *
    linarith

theorem actual_source_cutoff_rounding_is_fifteen_point_two_four :
    |sourceLogCutoff-(1524/100:ℝ)|<1/200 := by
  have hpL : (1/30:ℝ)^200<(4/5:ℝ)^3047 := by norm_num [div_pow]
  have hpU : (4/5:ℝ)^3049<(1/30:ℝ)^200 := by norm_num [div_pow]
  have hl : Real.log ((1/30:ℝ)^200)<Real.log ((4/5:ℝ)^3047) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpL
  have hu : Real.log ((4/5:ℝ)^3049)<Real.log ((1/30:ℝ)^200) :=
    (Real.log_lt_log_iff (by positivity) (by positivity)).mpr hpU
  rw [Real.log_pow,Real.log_pow] at hl hu
  have hq : Real.log (4/5:ℝ)<0 := Real.log_neg (by norm_num) (by norm_num)
  have hL : (3047/200:ℝ)<sourceLogCutoff := by
    rw [sourceLogCutoff,lt_div_iff_of_neg hq]
    norm_num at hl
    linarith
  have hU : sourceLogCutoff<(3049/200:ℝ) := by
    rw [sourceLogCutoff,div_lt_iff_of_neg hq]
    norm_num at hu
    linarith
  rw [abs_lt]
  constructor <;>linarith

theorem actual_source_fifteen_and_sixteen_bound_roundings :
    |sourceBound 15-(105553/1000000:ℝ)|<1/2000000 ∧
      |sourceBound 16-(844425/10000000:ℝ)|<1/20000000 := by
  norm_num [sourceBound]

theorem actual_source_initial_storage_energy_arithmetic_and_sequence_norm
    {E : Type*} [NormedAddCommGroup E] (output : E)
    (hcertificate : ‖output‖^2≤(4:ℝ)+4*9) :
    (4:ℝ)+4*9=40 ∧ ‖output‖≤Real.sqrt 40 ∧
      |Real.sqrt 40-(632456/100000:ℝ)|<1/200000 ∧
      (6:ℝ)<Real.sqrt 40 := by
  have hs:=Real.sq_sqrt (show (0:ℝ)≤40 by norm_num)
  refine ⟨by norm_num,?_,?_,?_⟩
  · nlinarith [norm_nonneg output,Real.sqrt_nonneg 40]
  · rw [abs_lt];constructor <;>nlinarith [Real.sqrt_nonneg 40]
  · nlinarith [Real.sqrt_nonneg 40]

theorem actual_zero_initial_storage_is_the_pure_gain_premise
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (input : E) (output : F) (hcertificate : ‖output‖^2≤(0:ℝ)+4*‖input‖^2) :
    ‖output‖≤2*‖input‖ := by
  nlinarith [norm_nonneg input,norm_nonneg output]

theorem actual_nonzero_initial_storage_cannot_be_dropped_from_the_source_inequality :
    (Real.sqrt 40)^2≤(4:ℝ)+4*3^2 ∧ ¬Real.sqrt 40≤2*3 := by
  have hs:=Real.sq_sqrt (show (0:ℝ)≤40 by norm_num)
  constructor
  · norm_num [hs]
  · have hp : (6:ℝ)<Real.sqrt 40 := by nlinarith [Real.sqrt_nonneg 40]
    norm_num;exact hp

end SafeLearning.CompleteModulesDesignContractionStorage
