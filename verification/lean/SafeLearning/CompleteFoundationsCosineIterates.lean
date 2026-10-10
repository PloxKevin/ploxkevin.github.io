import SafeLearning.CompleteFoundationsCosineNumerics

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 15000000
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsCosineIterates
open CompleteFoundationsCosineNumerics CompleteFoundationsCosineContraction

def sourceTable : Fin 33→ℝ×ℝ := ![
    ((1/1:ℝ),(1/1:ℝ)),
    ((27015115293/50000000000:ℝ),(5403023059/10000000000:ℝ)),
    ((85755321581/100000000000:ℝ),(85755321587/100000000000:ℝ)),
    ((32714489523/50000000000:ℝ),(32714489527/50000000000:ℝ)),
    ((7934803587/10000000000:ℝ),(39674017939/50000000000:ℝ)),
    ((35068438679/50000000000:ℝ),(70136877367/100000000000:ℝ)),
    ((15279193657/20000000000:ℝ),(15279193659/20000000000:ℝ)),
    ((36105121249/50000000000:ℝ),(18052560627/25000000000:ℝ)),
    ((75041776171/100000000000:ℝ),(75041776181/100000000000:ℝ)),
    ((73140404237/100000000000:ℝ),(9142550531/12500000000:ℝ)),
    ((18605933871/25000000000:ℝ),(14884747099/20000000000:ℝ)),
    ((73560474039/100000000000:ℝ),(1471209481/2000000000:ℝ)),
    ((14828501731/20000000000:ℝ),(37071254333/50000000000:ℝ)),
    ((36875344523/50000000000:ℝ),(73750689057/100000000000:ℝ)),
    ((74014733551/100000000000:ℝ),(37007366781/50000000000:ℝ)),
    ((73836920407/100000000000:ℝ),(36918460209/50000000000:ℝ)),
    ((9244590027/12500000000:ℝ),(73956720227/100000000000:ℝ)),
    ((36938015991/50000000000:ℝ),(73876031993/100000000000:ℝ)),
    ((36965194617/50000000000:ℝ),(14786077849/20000000000:ℝ)),
    ((36946887833/50000000000:ℝ),(73893775677/100000000000:ℝ)),
    ((18479609993/25000000000:ℝ),(73918439983/100000000000:ℝ)),
    ((73901826237/100000000000:ℝ),(9237728281/12500000000:ℝ)),
    ((4619563603/6250000000:ℝ),(73913017659/100000000000:ℝ)),
    ((73905479069/100000000000:ℝ),(1847636977/2500000000:ℝ)),
    ((73910557187/100000000000:ℝ),(36955278599/50000000000:ℝ)),
    ((2956285461/4000000000:ℝ),(14781427307/20000000000:ℝ)),
    ((73909440733/100000000000:ℝ),(73909440743/100000000000:ℝ)),
    ((36953944297/50000000000:ℝ),(14781577721/20000000000:ℝ)),
    ((14781786827/20000000000:ℝ),(36954467073/50000000000:ℝ)),
    ((73908229847/100000000000:ℝ),(36954114929/50000000000:ℝ)),
    ((9238588033/12500000000:ℝ),(2956348171/4000000000:ℝ)),
    ((73908384691/100000000000:ℝ),(36954192351/50000000000:ℝ)),
    ((73908599959/100000000000:ℝ),(7390859997/10000000000:ℝ))]

def lowerBound (n : ℕ) : ℝ := if h:n<33 then (sourceTable ⟨n,h⟩).1 else 0

def upperBound (n : ℕ) : ℝ := if h:n<33 then (sourceTable ⟨n,h⟩).2 else 1

theorem actual_rational_table_certificates (i : Fin 32) :
    0≤lowerBound i ∧ upperBound i≤1 ∧
      lowerBound (i.val+1)≤cosPoly (upperBound i)-1/80000000000 ∧
      cosPoly (lowerBound i)+1/80000000000≤upperBound (i.val+1) := by
  fin_cases i <;> norm_num [lowerBound,upperBound,sourceTable,cosPoly]

theorem actual_cosine_interval_transfer (x low high nextLow nextHigh : ℝ)
    (hx : x∈Icc low high) (hl : 0≤low) (hu : high≤1)
    (hnl : nextLow≤cosPoly high-1/80000000000)
    (hnu : cosPoly low+1/80000000000≤nextHigh) :
    Real.cos x∈Icc nextLow nextHigh := by
  have hh0 : 0≤high := hl.trans (hx.1.trans hx.2)
  have hl1 : low≤1 := (hx.1.trans hx.2).trans hu
  have eh := abs_le.mp (actual_real_cosine_uniform_rational_error high (by rw [abs_of_nonneg hh0];exact hu))
  have el := abs_le.mp (actual_real_cosine_uniform_rational_error low (by rw [abs_of_nonneg hl];exact hl1))
  have hcxlo := Real.cos_le_cos_of_nonneg_of_le_pi hl
    ((hx.2.trans hu).trans (by linarith [Real.pi_gt_three])) hx.1
  have hcxhi := Real.cos_le_cos_of_nonneg_of_le_pi (hl.trans hx.1)
    (by linarith [Real.pi_gt_three] : high≤Real.pi) hx.2
  constructor <;> linarith [eh.1,el.2]

theorem actual_source_first_thirty_two_iterations_enclosed (n : ℕ) (hn : n≤32) :
    Real.cos^[n] 1∈Icc (lowerBound n) (upperBound n) := by
  induction n with
  | zero => norm_num [lowerBound,upperBound,sourceTable]
  | succ n ih =>
    have hp := ih (by omega)
    have hc := actual_rational_table_certificates (⟨n,by omega⟩ : Fin 32)
    have h := actual_cosine_interval_transfer (Real.cos^[n] 1) (lowerBound n) (upperBound n)
      (lowerBound (n+1)) (upperBound (n+1)) hp hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    simpa only [Function.iterate_succ_apply'] using h

theorem actual_fixed_point_certified_enclosure :
    (7390851331/10000000000:ℝ)<(sourceFixedPoint:ℝ) ∧
      (sourceFixedPoint:ℝ)<7390851333/10000000000 := by
  have el := abs_le.mp (actual_real_cosine_uniform_rational_error (7390851331/10000000000) (by norm_num))
  have eu := abs_le.mp (actual_real_cosine_uniform_rational_error (7390851333/10000000000) (by norm_num))
  have hl : (7390851331/10000000000:ℝ)<Real.cos (7390851331/10000000000) := by
    norm_num [cosPoly] at el
    linarith [el.1]
  have hu : Real.cos (7390851333/10000000000)<(7390851333/10000000000:ℝ) := by
    norm_num [cosPoly] at eu
    linarith [eu.2]
  have hp := sourceFixedPoint.prop
  have hf := actual_fixed_point_and_uniqueness.1
  constructor
  · by_contra h
    have hx := Real.cos_le_cos_of_nonneg_of_le_pi
      (actual_cosine_one_positive_and_below_one.1.le.trans hp.1)
      (by linarith [Real.pi_gt_three] : (7390851331/10000000000:ℝ)≤Real.pi) (le_of_not_gt h)
    rw [hf] at hx
    linarith
  · by_contra h
    have hx := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ)≤7390851333/10000000000)
      (hp.2.trans (by linarith [Real.pi_gt_three])) (le_of_not_gt h)
    rw [hf] at hx
    linarith

theorem actual_thirty_two_iterations_meet_the_source_tolerance :
    |Real.cos^[32] 1-(sourceFixedPoint:ℝ)|<1/1000000 := by
  have hx := actual_source_first_thirty_two_iterations_enclosed 32 (by omega)
  have hf := actual_fixed_point_certified_enclosure
  norm_num [lowerBound,upperBound,sourceTable] at hx
  norm_num
  rw [abs_lt]
  constructor <;> linarith [hx.1,hx.2,hf.1,hf.2]

theorem actual_source_ninth_tenth_and_fixed_point_roundings :
    |Real.cos^[9] 1-(731404/1000000)|<1/2000000 ∧
    |Real.cos^[10] 1-(744237/1000000)|<1/2000000 ∧
    |(sourceFixedPoint:ℝ)-(739085/1000000)|<1/2000000 := by
  have h9 := actual_source_first_thirty_two_iterations_enclosed 9 (by omega)
  have h10 := actual_source_first_thirty_two_iterations_enclosed 10 (by omega)
  have hf := actual_fixed_point_certified_enclosure
  norm_num [lowerBound,upperBound,sourceTable] at h9 h10
  norm_num
  constructor
  · rw [abs_lt];constructor <;> linarith [h9.1,h9.2]
  constructor
  · rw [abs_lt];constructor <;> linarith [h10.1,h10.2]
  · rw [abs_lt];constructor <;> linarith [hf.1,hf.2]

end SafeLearning.CompleteFoundationsCosineIterates
