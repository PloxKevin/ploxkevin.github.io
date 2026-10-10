import SafeLearning.CompleteAppliedSequentialCalibration

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SafeLearning.CompleteAppliedCalibrationAverages

def averageError {Ω : Type*} (n : ℕ) (X : Option (Fin n)→Ω→ℝ) : Ω→ℝ :=
  fun omega=>X none omega+(n:ℝ)⁻¹*∑i:Fin n,X (some i) omega
def contributionWeight (n : ℕ) : Option (Fin n)→ℝ
  | none=>1
  | some _=>(n:ℝ)⁻¹

theorem actual_average_keeps_the_shared_offset_only_once
    {Ω : Type*} (n : ℕ) (X : Option (Fin n)→Ω→ℝ) :
    averageError n X=∑i:Option (Fin n),fun omega=>contributionWeight n i*X i omega := by
  funext omega
  simp [averageError,contributionWeight,Fintype.sum_option,Finset.mul_sum]

theorem actual_independent_noise_average_has_the_derived_variance_floor
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (n : ℕ) (hn : 0<n) (X : Option (Fin n)→Ω→ℝ)
    (hL2 : ∀i,MemLp (X i) 2 P) (hindep : iIndepFun X P)
    (hoffset : Var[X none;P]=2/3) (hnoise : ∀i:Fin n,Var[X (some i);P]=1) :
    Var[averageError n X;P]=2/3+1/(n:ℝ) := by
  classical
  let weighted : Option (Fin n)→Ω→ℝ := fun i omega=>contributionWeight n i*X i omega
  have hwL2 : ∀i,MemLp (weighted i) 2 P := fun i=>(hL2 i).const_mul _
  have hwIndep : Set.Pairwise (↑(Finset.univ:Finset (Option (Fin n))))
      (fun i j=>IndepFun (weighted i) (weighted j) P) := by
    intro i hi j hj hij
    exact (hindep.indepFun hij).comp (show Measurable (fun x:ℝ=>contributionWeight n i*x) by fun_prop)
      (show Measurable (fun x:ℝ=>contributionWeight n j*x) by fun_prop)
  rw [actual_average_keeps_the_shared_offset_only_once]
  change Var[∑i:Option (Fin n),weighted i;P]=_
  rw [IndepFun.variance_sum (fun i _=>hwL2 i) hwIndep]
  simp only [weighted,variance_const_mul,Fintype.sum_option,contributionWeight,
    one_pow,one_mul,hoffset,hnoise]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  have hnn : (n:ℝ)≠0 := by exact_mod_cast ne_of_gt hn
  field_simp
  <;> ring

theorem actual_distinct_reading_errors_have_the_shared_offset_covariance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (n : ℕ) (X : Option (Fin n)→Ω→ℝ)
    (hL2 : ∀i,MemLp (X i) 2 P) (hindep : iIndepFun X P)
    (hoffset : Var[X none;P]=2/3) (i j : Fin n) (hij : i≠j) :
    covariance (fun omega=>X none omega+X (some i) omega)
      (fun omega=>X none omega+X (some j) omega) P=2/3 := by
  have hni := (hindep.indepFun (show (none:Option (Fin n))≠some i by simp)).covariance_eq_zero
    (hL2 none) (hL2 (some i))
  have hnj := (hindep.indepFun (show (none:Option (Fin n))≠some j by simp)).covariance_eq_zero
    (hL2 none) (hL2 (some j))
  have hnij := (hindep.indepFun (show (some i:Option (Fin n))≠some j from
    fun h=>hij (Option.some.inj h))).covariance_eq_zero (hL2 (some i)) (hL2 (some j))
  change covariance (X none+X (some i)) (X none+X (some j)) P=_
  rw [covariance_add_left (hL2 none) (hL2 (some i)) ((hL2 none).add (hL2 (some j))),
    covariance_add_right (hL2 none) (hL2 none) (hL2 (some j)),
    covariance_add_right (hL2 (some i)) (hL2 none) (hL2 (some j)),
    covariance_self (hL2 none).aemeasurable,hoffset,hnj,hnij,
    covariance_comm (X (some i)) (X none),hni]
  norm_num

theorem actual_variance_floor_limit_and_hundred_reading_value :
    Tendsto (fun n:ℕ=>(2/3:ℝ)+1/(n:ℝ)) atTop (𝓝 (2/3)) ∧
      (2/3:ℝ)+1/100=203/300 ∧
      |(203/300:ℝ)-(67667/100000)|<1/200000 ∧
      (203/300:ℝ)≠(5/3)/100 ∧
      |Real.sqrt (2/3:ℝ)-(8165/10000)|<1/20000 := by
  refine ⟨?_,by norm_num,by norm_num,by norm_num,?_⟩
  · simpa using tendsto_const_nhds.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ))
  · have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2/3)
    have hp := Real.sqrt_nonneg (2/3:ℝ)
    rw [abs_lt];constructor <;> nlinarith

end SafeLearning.CompleteAppliedCalibrationAverages
