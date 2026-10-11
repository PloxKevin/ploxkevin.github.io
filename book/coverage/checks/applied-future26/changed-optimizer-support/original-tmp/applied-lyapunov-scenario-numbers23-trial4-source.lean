import SafeLearning.CompleteAppliedDiscountedHorizons
import SafeLearning.CompleteFoundationsExponentialNumerics
import SafeLearning.CompleteAppliedBinomialModel
import SafeLearning.CompleteAppliedValidation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option exponentiation.threshold 2000
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace SafeLearning.CompleteLyapunovScenarioNumbers23

def binomialMass (n i : ℕ) (p : ℝ) : ℝ :=
  (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i)

def lowerTail (n d : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, binomialMass n i p

private theorem mass_successor (n i : ℕ) (p : ℝ) (hi : i + 1 ≤ n) :
    binomialMass (n+1) (i+1) p =
      (1-p)*binomialMass n (i+1) p + p*binomialMass n i p := by
  have he : n-i = (n-(i+1))+1 := by omega
  have he' : n+1-(i+1) = n-i := by omega
  simp only [binomialMass, Nat.choose_succ_succ', Nat.cast_add, he', he, pow_succ]
  ring

private theorem tail_successor_split (n m : ℕ) (p : ℝ) (hm : m ≤ n) :
    lowerTail (n+1) (m+1) p =
      (1-p)*lowerTail n (m+1) p + p*lowerTail n m p := by
  induction m with
  | zero => simp [lowerTail, binomialMass, pow_succ]; ring
  | succ m ih =>
    have hmn : m ≤ n := by omega
    have hs := mass_successor n m p (by omega)
    simp only [lowerTail, Finset.sum_range_succ] at ih ⊢
    have hh := ih hmn
    rw [hs]
    linarith

theorem actual_binomial_tail_successor_identity (n m : ℕ) (p : ℝ) (hm : m ≤ n) :
    lowerTail (n+1) (m+1) p =
      lowerTail n (m+1) p - p*binomialMass n m p := by
  rw [tail_successor_split n m p hm]
  have he : lowerTail n (m+1) p = lowerTail n m p + binomialMass n m p := by
    simp [lowerTail, Finset.sum_range_succ]
  rw [he]
  ring

theorem actual_binomial_tail_nonincrease (n m : ℕ) (p : ℝ)
    (hm : m ≤ n) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    lowerTail (n+1) (m+1) p ≤ lowerTail n (m+1) p := by
  rw [actual_binomial_tail_successor_identity n m p hm]
  have hn : 0 ≤ p*binomialMass n m p := by
    unfold binomialMass
    positivity
  linarith

theorem actual_ten_term_tail_antitone_from_nine :
    Antitone (fun k : ℕ => lowerTail (k+9) 10 (1/20)) := by
  apply antitone_nat_of_succ_le
  intro k
  convert actual_binomial_tail_nonincrease (k+9) 9 (1/20) (by omega)
    (by norm_num) (by norm_num) using 1

theorem actual_dimension_one_reduction (n : ℕ) (p : ℝ) :
    lowerTail n 1 p = (1-p)^n := by simp [lowerTail,binomialMass]

theorem actual_independent_count_lower_tail_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n d : ℕ) (A : Fin n → Set Ω) (hA : ∀ i,MeasurableSet (A i))
    (hind : iIndepSet A P) (p : ℝ) (hp : ∀ i,P.real (A i)=p) :
    P.real {w | CompleteAppliedFailureCounts.failureCount A w < d}=lowerTail n d p := by
  classical
  have he : {w | CompleteAppliedFailureCounts.failureCount A w < d}=
      ⋃ i∈Finset.range d,{w | CompleteAppliedFailureCounts.failureCount A w=i} := by
    ext w
    simp only [Set.mem_setOf_eq,Set.mem_iUnion,Finset.mem_range]
    constructor
    · intro h;exact ⟨_,h,rfl⟩
    · rintro ⟨i,hi,he⟩;omega
  have hd : Set.PairwiseDisjoint (Finset.range d : Set ℕ)
      (fun i=>{w | CompleteAppliedFailureCounts.failureCount A w=i}) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    exact hij (hwi.symm.trans hwj)
  rw [he,measureReal_biUnion_finset hd
    (fun i _ => (measurableSet_singleton i).preimage
      (CompleteAppliedBinomialModel.failure_count_measurable A hA))]
  unfold lowerTail
  apply Finset.sum_congr rfl
  intro i hi
  exact CompleteAppliedBinomialModel.actual_binomial_count_mass P n A hA hind p hp i

theorem actual_one_dimensional_boundary_and_rounding :
    (1/1000:ℝ)<(19/20)^134 ∧ (19/20:ℝ)^135<1/1000 ∧
      |Real.log 1000/Real.log (20/19)-1347/10|<1/20 := by
  obtain ⟨hl,hu,_,_⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  obtain ⟨_,_,h100l,h100u⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  have he1000 : Real.log 1000=(3/2:ℝ)*Real.log 100 := by
    have he : Real.log 1000=3*Real.log 10 := by
      rw [show (1000:ℝ)=(10:ℝ)^3 by norm_num,Real.log_pow]; norm_num
    have he' : Real.log 100=2*Real.log 10 := by
      rw [show (100:ℝ)=(10:ℝ)^2 by norm_num,Real.log_pow]; norm_num
    linarith
  have h1000l : (6907754/1000000:ℝ)<Real.log 1000 := by rw [he1000]; linarith
  have h1000u : Real.log 1000<(6907756/1000000:ℝ) := by rw [he1000]; linarith
  have hd : 0<Real.log (20/19:ℝ) := by linarith
  refine ⟨by norm_num,by norm_num,?_⟩
  rw [abs_lt]
  constructor
  · have h := (lt_div_iff₀ hd).mpr
      (show (1347/10-1/20)*Real.log (20/19)<Real.log 1000 by linarith)
    linarith
  · have h := (div_lt_iff₀ hd).mpr
      (show Real.log 1000<(1347/10+1/20)*Real.log (20/19) by linarith)
    linarith

theorem actual_least_one_dimensional_sample_size (n : ℕ) :
    lowerTail n 1 (1/20) ≤ 1/1000 ↔ 135 ≤ n := by
  rw [actual_dimension_one_reduction]
  norm_num only [show (1-(1/20:ℝ))=19/20 by norm_num]
  constructor
  · intro h
    by_contra hh
    have hn : n ≤ 134 := by omega
    have hm := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤19/20)
      (by norm_num : (19/20:ℝ)≤1) hn
    exact not_le_of_gt actual_one_dimensional_boundary_and_rounding.1 (hm.trans h)
  · intro hn
    exact (pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤19/20)
      (by norm_num : (19/20:ℝ)≤1) hn).trans
      actual_one_dimensional_boundary_and_rounding.2.1.le

theorem actual_one_dimensional_logarithmic_threshold (n : ℕ) :
    lowerTail n 1 (1/20) ≤ 1/1000 ↔
      Real.log 1000/Real.log (20/19) ≤ (n:ℝ) := by
  rw [actual_dimension_one_reduction]
  have hd : 0<Real.log (20/19:ℝ) := Real.log_pos (by norm_num)
  have hi : Real.log (1-(1/20:ℝ))= -Real.log (20/19) := by
    rw [show (1-(1/20:ℝ))=(20/19)⁻¹ by norm_num,Real.log_inv]
  have hb : Real.log (1/1000:ℝ)= -Real.log 1000 := by
    rw [show (1/1000:ℝ)=(1000:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [←Real.log_le_log_iff (pow_pos (by norm_num : (0:ℝ)<1-1/20) n)
    (by norm_num),Real.log_pow,hi,hb,div_le_iff₀ hd]
  constructor <;> intro h <;> linarith

theorem actual_ten_variable_boundary_enclosures :
    (10030776/10^12:ℝ)<lowerTail 580 10 (1/20) ∧
      lowerTail 580 10 (1/20)<10030778/10^12 ∧
      (9672779/10^12:ℝ)<lowerTail 581 10 (1/20) ∧
      lowerTail 581 10 (1/20)<9672782/10^12 := by
  norm_num [lowerTail,binomialMass,Finset.sum_range_succ,
    Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

theorem actual_ten_variable_source_roundings_and_crossing :
    |lowerTail 581 10 (1/20)-967/10^8|<1/(2*10^8) ∧
      |lowerTail 580 10 (1/20)-1003/10^8|<1/(2*10^8) ∧
      lowerTail 581 10 (1/20)<1/100000 ∧
      (1/100000:ℝ)<lowerTail 580 10 (1/20) := by
  obtain ⟨a,b,c,d⟩ := actual_ten_variable_boundary_enclosures
  constructor
  · rw [abs_lt]; constructor <;> linarith
  constructor
  · rw [abs_lt]; constructor <;> linarith
  constructor <;> linarith

theorem actual_least_ten_variable_sample_size (n : ℕ) :
    lowerTail n 10 (1/20) ≤ 1/100000 ↔ 581 ≤ n := by
  have hm := actual_ten_term_tail_antitone_from_nine
  have hc := actual_ten_variable_source_roundings_and_crossing
  constructor
  · intro hh
    by_contra hn
    have hn' : n ≤ 580 := by omega
    by_cases hs : 9 ≤ n
    · have hh' := hm (show n-9 ≤ 571 by omega)
      have he : n-9+9=n := by omega
      norm_num only [he,show (571+9:ℕ)=580 by rfl] at hh'
      exact not_le_of_gt hc.2.2.2 (hh'.trans hh)
    · have hn9 : n ≤ 9 := by omega
      have hzero : (19/20:ℝ)^n ≤ lowerTail n 10 (1/20) := by
        have hh0 := Finset.single_le_sum (f:=fun i=>binomialMass n i (1/20))
          (fun i _=>by unfold binomialMass; positivity)
          (show 0∈Finset.range 10 by decide)
        have he0 : binomialMass n 0 (1/20)=(19/20:ℝ)^n := by
          simp only [binomialMass,Nat.choose_zero,Nat.cast_one,pow_zero,
            one_mul,Nat.sub_zero]
          norm_num
        rw [he0] at hh0
        exact hh0
      have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ)≤19/20)
        (by norm_num : (19/20:ℝ)≤1) hn9
      have hnum : (1/100000:ℝ)<(19/20)^9 := by norm_num
      exact not_le_of_gt hnum (hp.trans (hzero.trans hh))
  · intro hn
    have hh := hm (show 572 ≤ n-9 by omega)
    have he : n-9+9=n := by omega
    norm_num only [he,show (572+9:ℕ)=581 by rfl] at hh
    exact hh.trans hc.2.2.1.le

theorem actual_common_lyapunov_variable_count :
    (2*2^2+2*1:ℕ)=10 := by norm_num

theorem actual_logarithm_five_decades :
    Real.log 100000=(5/2:ℝ)*Real.log 100 := by
  have he : Real.log 100000=5*Real.log 10 := by
    rw [show (100000:ℝ)=(10:ℝ)^5 by norm_num,Real.log_pow]; norm_num
  have he' : Real.log 100=2*Real.log 10 := by
    rw [show (100:ℝ)=(10:ℝ)^2 by norm_num,Real.log_pow]; norm_num
  linarith

theorem actual_sufficient_threshold_enclosure_and_least_integer :
    (8605169/10000:ℝ)<40*(Real.log 100000+10) ∧
      40*(Real.log 100000+10)<8605172/10000 ∧
      Nat.ceil (40*(Real.log 100000+10))=861 ∧
      |((861-581:ℝ)/581)-48/100|<1/200 := by
  obtain ⟨_,_,hl,hu⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  rw [actual_logarithm_five_decades]
  have hb : (8605169/10000:ℝ)<40*(5/2*Real.log 100+10) ∧
      40*(5/2*Real.log 100+10)<8605172/10000 := by constructor <;> linarith
  refine ⟨hb.1,hb.2,?_,by norm_num⟩
  apply Nat.ceil_eq_iff (by norm_num : (861:ℕ)≠0) |>.mpr
  constructor <;> norm_num <;> linarith [hb.1,hb.2]

theorem actual_validation_thresholds_rounding_and_ceilings :
    |Real.log 100/(2*(1/50:ℝ)^2)-57565/10|<1/20 ∧
      |Real.log 100/(2*(1/50:ℝ))-1151/10|<1/20 ∧
      Nat.ceil (Real.log 100/(2*(1/50:ℝ)^2))=5757 ∧
      Nat.ceil (Real.log 100/(2*(1/50:ℝ)))=116 := by
  obtain ⟨_,_,hl,hu⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  have he : Real.log 100/(2*(1/50:ℝ)^2)=1250*Real.log 100 := by ring
  have he' : Real.log 100/(2*(1/50:ℝ))=25*Real.log 100 := by ring
  rw [he,he']
  refine ⟨?_,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> linarith
  · apply (Nat.ceil_eq_iff (by norm_num : (5757:ℕ)≠0)).mpr
    constructor <;> norm_num <;> linarith
  · apply (Nat.ceil_eq_iff (by norm_num : (116:ℕ)≠0)).mpr
    constructor <;> norm_num <;> linarith

theorem actual_validation_exponential_bound_iff_threshold (n : ℕ) :
    Real.exp (-2*(n:ℝ)*(1/50)^2)≤1/100 ↔
      Real.log 100/(2*(1/50:ℝ)^2)≤(n:ℝ) := by
  rw [show (1/100:ℝ)=Real.exp (-Real.log 100) by
    rw [Real.exp_neg,Real.exp_log (by norm_num)];norm_num,Real.exp_le_exp,
    div_le_iff₀ (by norm_num : (0:ℝ)<2*(1/50)^2)]
  constructor <;> intro h <;> linarith

theorem actual_least_validation_size (n : ℕ) :
    Real.exp (-2*(n:ℝ)*(1/50)^2)≤1/100 ↔ 5757≤n := by
  rw [actual_validation_exponential_bound_iff_threshold]
  have he := actual_validation_thresholds_rounding_and_ceilings.2.2.1
  rw [←Nat.ceil_le]
  rw [he]

theorem actual_misprinted_size_exponent_and_rigorous_rounding :
    -2*(116:ℝ)*(1/50)^2= -116/1250 ∧
      (91137575/10^8:ℝ)<Real.exp (-116/1250) ∧
      Real.exp (-116/1250)<91137577/10^8 ∧
      |Real.exp (-116/1250)-911/1000|<1/2000 ∧
      |(1-Real.exp (-116/1250))-9/100|<1/200 ∧
      (1-Real.exp (-116/1250):ℝ)<9/100 := by
  have h := CompleteFoundationsExponentialNumerics.actual_twentieth_exponential_polynomial_error_on_the_unit_interval
    (-116/1250) (by norm_num)
  norm_num [CompleteFoundationsExponentialNumerics.expPolynomial,Finset.sum_range_succ,
    Nat.factorial,abs_le] at h
  have hb : (91137575/10^8:ℝ)<Real.exp (-116/1250) ∧
      Real.exp (-116/1250)<91137577/10^8 := by constructor <;> linarith [h.1,h.2]
  refine ⟨by norm_num,hb.1,hb.2,?_,?_,?_⟩
  · rw [abs_lt];constructor <;> linarith [hb.1,hb.2]
  · rw [abs_lt];constructor <;> linarith [hb.1,hb.2]
  · linarith [hb.1]

theorem actual_printed_decimal_equalities_are_false :
    Real.log 100/(2*(1/50:ℝ)^2)≠57565/10 ∧
      Real.log 100/(2*(1/50:ℝ))≠1151/10 ∧
      Real.exp (-116/1250)≠911/1000 := by
  obtain ⟨_,_,hl,hu⟩ :=
    CompleteAppliedDiscountedHorizons.actual_discount_log_enclosure_and_log_hundred_enclosure
  have he : Real.log 100/(2*(1/50:ℝ)^2)=1250*Real.log 100 := by ring
  have he' : Real.log 100/(2*(1/50:ℝ))=25*Real.log 100 := by ring
  refine ⟨?_,?_,?_⟩
  · rw [he];intro h;linarith
  · rw [he'];intro h;linarith
  · intro h;have hb:=actual_misprinted_size_exponent_and_rigorous_rounding.2.1
    rw [h] at hb;norm_num at hb

theorem actual_corrected_posterior_lower_bound_arithmetic :
    (19/20:ℝ)-1/20-1/50=22/25 ∧
      (19/20:ℝ)*(1-1/20-1/50)=1767/2000 ∧
      (22/25:ℝ)≤(19/20)*(1-1/20-1/50) := by norm_num

end SafeLearning.CompleteLyapunovScenarioNumbers23
