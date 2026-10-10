import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SafeLearning.CompleteFoundationsDiscountHorizons
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem actual_finite_geometric_induction (q : ℝ) (hq : q≠1) (T : ℕ) :
    (∑ t∈Finset.range T,q^t)=(1-q^T)/(1-q) := by
  have hd : 1-q≠0 := by exact sub_ne_zero.mpr (Ne.symm hq)
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring

def triangularTerm (q : ℝ) (t s : ℕ) : ℝ := if s<t then q^t else 0

theorem actual_triangular_nonnegative (q : ℝ) (hq : 0≤q) (t s : ℕ) :
    0≤triangularTerm q t s := by unfold triangularTerm;split_ifs <;> positivity

theorem actual_row_sum (q : ℝ) (t : ℕ) :
    (∑' s,triangularTerm q t s)=(t:ℝ)*q^t := by
  rw [tsum_eq_sum (s:=Finset.range t) (by
    intro s hs
    have hst : ¬s<t := by simpa only [Finset.mem_range] using hs
    simp only [triangularTerm,ite_eq_right hst])]
  calc
    _ = ∑ _s∈Finset.range t,q^t := by
      apply Finset.sum_congr rfl
      intro s hs;simp [triangularTerm,Finset.mem_range.mp hs]
    _ = _ := by simp

theorem actual_row_summable (q : ℝ) (t : ℕ) : Summable (triangularTerm q t) := by
  apply summable_of_ne_finset_zero (s:=Finset.range t)
  intro s hs
  have hst : ¬s<t := by simpa only [Finset.mem_range] using hs
  simp only [triangularTerm,ite_eq_right hst]

theorem actual_nonnegative_exchange (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    Summable (fun p : ℕ×ℕ=>triangularTerm q p.1 p.2) ∧
    (∑' t,∑' s,triangularTerm q t s)=(∑' s,∑' t,triangularTerm q t s) := by
  have hnorm : ‖q‖<1 := by rwa [Real.norm_eq_abs,abs_of_nonneg hq0]
  have hsum : Summable (fun p : ℕ×ℕ=>triangularTerm q p.1 p.2) :=
    (summable_prod_of_nonneg (fun p=>actual_triangular_nonnegative q hq0 p.1 p.2)).mpr
      ⟨actual_row_summable q,by
        simp only [actual_row_sum]
        exact (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable⟩
  exact ⟨hsum,hsum.tsum_comm.symm⟩

theorem actual_tail_column (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) (s : ℕ) :
    (∑' t,triangularTerm q t s)=q^(s+1)/(1-q) := by
  have hg := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (q^(s+1))
  have hs : HasSum (fun t=>triangularTerm q (t+(s+1)) s) (q^(s+1)/(1-q)) := by
    convert hg using 1
    · funext t
      have hst : s<t+(s+1) := by omega
      simp only [triangularTerm,ite_eq_left hst,pow_add];ring
    · ring
  have h := hs.sum_range_add (f:=fun t=>triangularTerm q t s) (k:=s+1)
  have hz : (∑ t∈Finset.range (s+1),triangularTerm q t s)=0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have : ¬s<t := by have := Finset.mem_range.mp ht;omega
    simp [triangularTerm,this]
  rw [hz,zero_add] at h
  exact h.tsum_eq

theorem actual_source_two_tail_derivation (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    (∑' t : ℕ,(t:ℝ)*q^t)=
      (∑' s : ℕ,q^(s+1)/(1-q)) ∧
    (∑' s : ℕ,q^(s+1)/(1-q))=q/(1-q)^2 := by
  constructor
  · have h := (actual_nonnegative_exchange q hq0 hq1).2
    simpa only [actual_row_sum,actual_tail_column q hq0 hq1] using h
  · have h := ((hasSum_geometric_of_lt_one hq0 hq1).mul_left (q/(1-q))).tsum_eq
    convert h using 1
    · apply tsum_congr;intro s;rw [pow_succ];ring
    · field_simp [show 1-q≠0 by linarith]

def horizonParameter (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) : unitInterval :=
  ⟨1-q,by constructor <;> linarith⟩
def horizonLaw (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) : Measure ℕ :=
  geometricMeasure (horizonParameter q hq0 hq1)

theorem actual_horizon_probability_measure (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    IsProbabilityMeasure (horizonLaw q hq0 hq1) := by unfold horizonLaw;infer_instance

theorem actual_horizon_atoms (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) (t : ℕ) :
    (horizonLaw q hq0 hq1).real {t}=(1-q)*q^t := by
  have hp : horizonParameter q hq0 hq1≠0 := by
    intro he;have := congrArg (fun x : unitInterval => (x:ℝ)) he
    dsimp [horizonParameter] at this
    linarith
  rw [horizonLaw,geometricMeasure_real_singleton hp]
  simp [horizonParameter]
  ring

theorem actual_horizon_integrable_and_mean (q : ℝ) (hq0 : 0≤q) (hq1 : q<1) :
    Integrable (fun t : ℕ=>(t:ℝ)) (horizonLaw q hq0 hq1) ∧
    (∫ t : ℕ,(t:ℝ) ∂horizonLaw q hq0 hq1)=q/(1-q) := by
  have hp : horizonParameter q hq0 hq1≠0 := by
    intro he;have := congrArg (fun x : unitInterval => (x:ℝ)) he
    dsimp [horizonParameter] at this
    linarith
  have hg : HasSum (fun t : ℕ=>(t:ℝ)*q^t) (q/(1-q)^2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by rwa [Real.norm_eq_abs,abs_of_nonneg hq0])
  have hs : HasSum (fun t : ℕ=>q^t*(1-q)*(t:ℝ)) (q/(1-q)) := by
    convert hg.mul_left (1-q) using 1
    · funext t;ring
    · field_simp [show 1-q≠0 by linarith]
  have hi : Integrable (fun t : ℕ=>(t:ℝ)) (horizonLaw q hq0 hq1) := by
    rw [horizonLaw,integrable_geometricMeasure_iff hp]
    simpa [horizonParameter,Real.norm_eq_abs] using hs.summable
  refine ⟨hi,?_⟩
  have h := hasSum_integral_geometricMeasure hp hi
  have he : (fun t : ℕ => ((1-(horizonParameter q hq0 hq1):ℝ)^t *
      (horizonParameter q hq0 hq1:ℝ)) • (t:ℝ))=(fun t : ℕ=>q^t*(1-q)*(t:ℝ)) := by
    funext t;simp [horizonParameter,smul_eq_mul]
  rw [he] at h
  exact h.unique hs

theorem actual_source_discount_horizon_numbers :
    (∑' t : ℕ,(t:ℝ)*(9/10:ℝ)^t)=90 ∧
    (∫ t : ℕ,(t:ℝ) ∂horizonLaw (9/10) (by norm_num) (by norm_num))=9 := by
  constructor
  · rw [(actual_source_two_tail_derivation (9/10) (by norm_num) (by norm_num)).1,
      (actual_source_two_tail_derivation (9/10) (by norm_num) (by norm_num)).2]
    norm_num
  · rw [(actual_horizon_integrable_and_mean (9/10) (by norm_num) (by norm_num)).2]
    norm_num

end SafeLearning.CompleteFoundationsDiscountHorizons
