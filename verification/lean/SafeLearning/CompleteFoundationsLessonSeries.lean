import SafeLearning.CompleteFoundationsDiscountHorizons
import SafeLearning.CompleteFoundationsSeries
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsLessonSeries
open Filter
open scoped BigOperators Topology
open SafeLearning.CompleteFoundationsDiscountHorizons

def partialSum (a : ℕ→ℝ) (T : ℕ) : ℝ := ∑ t∈Finset.range T,a t
def seriesHasLimit (a : ℕ→ℝ) (v : ℝ) : Prop := Tendsto (partialSum a) atTop (𝓝 v)

theorem actual_finite_geometric_cancellation (q : ℝ) (T : ℕ) :
    partialSum (fun t=>q^t) T-q*partialSum (fun t=>q^t) T=1-q^T := by
  by_cases hq : q=1
  · subst q;simp [partialSum]
  · rw [partialSum,actual_finite_geometric_induction q hq]
    field_simp [show 1-q≠0 by exact sub_ne_zero.mpr (Ne.symm hq)]

theorem actual_signed_geometric_series (q : ℝ) (hq : |q|<1) :
    HasSum (fun t : ℕ=>q^t) (1/(1-q)) ∧
    seriesHasLimit (fun t=>q^t) (1/(1-q)) ∧
    Tendsto (fun T : ℕ=>|q|^T) atTop (𝓝 0) := by
  have hs : HasSum (fun t : ℕ=>q^t) (1/(1-q)) := by
    simpa only [one_div] using hasSum_geometric_of_norm_lt_one (show ‖q‖<1 from hq)
  refine ⟨hs,hs.tendsto_sum_nat,?_⟩
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg q) hq

theorem actual_signed_geometric_tail (q : ℝ) (hq : |q|<1) (T : ℕ) :
    HasSum (fun t : ℕ=>q^(t+T)) (q^T/(1-q)) := by
  have hs := (actual_signed_geometric_series q hq).1.mul_left (q^T)
  convert hs using 1
  · funext t;rw [pow_add];ring
  · ring

theorem actual_geometric_prefix_tail_identity (q : ℝ) (hq : |q|<1) (T : ℕ) :
    partialSum (fun t=>q^t) T+(∑' t : ℕ,q^(t+T))=1/(1-q) ∧
    1/(1-q)-partialSum (fun t=>q^t) T=q^T/(1-q) := by
  have hn : q≠1 := by intro he;subst q;norm_num at hq
  have hfinite := actual_finite_geometric_induction q hn T
  have htail := (actual_signed_geometric_tail q hq T).tsum_eq
  rw [partialSum,hfinite,htail]
  constructor <;> ring

theorem actual_bounded_discounted_return_and_tail (q R : ℝ) (a : ℕ→ℝ)
    (hq0 : 0≤q) (hq1 : q<1) (ha : ∀ t,|a t|≤R) (T : ℕ) :
    Summable (fun t=>q^t*a t) ∧
    |∑' t,q^t*a t|≤R/(1-q) ∧
    |∑' t : ℕ,q^(t+T)*a (t+T)|≤q^T*R/(1-q) := by
  have hr := SafeLearning.CompleteFoundationsSeries.discounted_return_bound a q R hq0 hq1 ha
  have ht := SafeLearning.CompleteFoundationsSeries.discounted_tail_bound a q R T hq0 hq1 ha
  exact ⟨hr.1,hr.2,by simpa only [mul_comm R] using ht⟩

theorem actual_effective_horizon_example :
    (1/(1-(99/100:ℝ)))=100 ∧ (∑' t : ℕ,(99/100:ℝ)^t)=100 := by
  constructor
  · norm_num
  · rw [(actual_signed_geometric_series (99/100) (by norm_num)).1.tsum_eq]
    norm_num

end SafeLearning.CompleteFoundationsLessonSeries
