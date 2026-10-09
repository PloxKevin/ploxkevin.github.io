import SafeLearning.CompleteAppliedExercises
import SafeLearning.CompleteAppliedFiniteClaims
import SafeLearning.CompleteAppliedElementary
import SafeLearning.CompleteAppliedPolicyModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedExerciseModels
open MeasureTheory ProbabilityTheory Filter
open SafeLearning.CompleteAppliedExercises SafeLearning.CompleteAppliedProbability
open scoped ENNReal NNReal Topology

theorem hypothetical_detector_counts :
    (1000:ℝ)*(1/10)=100 ∧ 1000*(9/10:ℝ)=900 ∧
    1000*(2/25:ℝ)=80 ∧ 1000*(9/50:ℝ)=180 ∧ 1000*(13/50:ℝ)=260 ∧
    (80/260:ℝ)=4/13 := by norm_num

theorem ready_outer_product_matrix :
    Matrix.vecMulVec (![1,2] : Fin 2 → ℝ) ![1,2]=!![1,2;2,4] := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMulVec]

theorem covariance_quadratic_nonnegative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (u v : ℝ) :
    0≤u^2*variance X μ+2*u*v*covariance X Y μ+v^2*variance Y μ := by
  have hh := variance_nonneg (fun omega => u*X omega+v*Y omega) μ
  change 0≤variance ((fun omega => u*X omega)+(fun omega => v*Y omega)) μ at hh
  rw [variance_add (hX.const_mul u) (hY.const_mul v),variance_const_mul,
    variance_const_mul,covariance_const_mul_left,covariance_const_mul_right] at hh
  nlinarith

theorem safe_optimistic_exact_set :
    {a : Fin 2 | 0≤(![(3/10:ℝ)-2/5,1/5-1/10] : Fin 2 → ℝ) a}={1} ∧
    (∀ a ∈ ({1} : Set (Fin 2)),
      (![(1/2:ℝ)+1/5,3/5+1/20] : Fin 2 → ℝ) a≤13/20) := by
  constructor
  · ext a; fin_cases a <;> norm_num
  · intro a ha
    simp only [Set.mem_singleton_iff] at ha
    subst a
    norm_num

theorem short_return_recursion :
    (∑' n : ℕ, (1/2:ℝ)^n*finiteTrajectoryReward n)=
      finiteTrajectoryReward 0+(1/2)*(∑' n : ℕ, (1/2:ℝ)^n*finiteTrajectoryReward (n+1)) := by
  rw [short_return.1,short_return.2]
  norm_num [finiteTrajectoryReward]

def policyAViolation (_t : Fin 100) (outcome : Fin 2) : ℝ := if outcome=0 then 1 else 0
def policyBViolation (t : Fin 100) (_outcome : Fin 2) : ℝ := if t=0 then 1 else 0

theorem source_violation_counts (outcome : Fin 2) :
    (∑ t : Fin 100, policyAViolation t outcome)=rareViolationCount outcome ∧
    (∑ t : Fin 100, policyBViolation t outcome)=1 := by
  constructor
  · fin_cases outcome <;> norm_num [policyAViolation,rareViolationCount]
  · simp [policyBViolation]

theorem source_any_violation_events :
    {i : Fin 2 | ∃ t : Fin 100, policyAViolation t i=1}={i | 0<rareViolationCount i} ∧
    {i : Fin 2 | ∃ t : Fin 100, policyBViolation t i=1}=Set.univ := by
  constructor
  · ext i; fin_cases i <;> norm_num [policyAViolation,rareViolationCount]
  · ext i; simp only [Set.mem_setOf_eq,Set.mem_univ,iff_true]
    exact ⟨0,by norm_num [policyBViolation]⟩

def alternatingReward (n : ℕ) : ℝ := if n%2=0 then 1 else 0

theorem alternating_return :
    HasSum (fun n : ℕ => (1/2:ℝ)^n*alternatingReward n) (4/3) := by
  have hg := hasSum_geometric_of_abs_lt_one (by norm_num : |(1/4:ℝ)|<1)
  norm_num at hg
  have he : HasSum (fun n : ℕ => (1/2:ℝ)^(2*n)*alternatingReward (2*n)) (4/3) := by
    convert hg using 1
    ext n; simp [alternatingReward,pow_mul]; norm_num
  have ho : HasSum (fun n : ℕ => (1/2:ℝ)^(2*n+1)*alternatingReward (2*n+1)) 0 := by
    convert hasSum_zero using 1
    ext n; simp [alternatingReward]
  simpa only [add_zero] using (HasSum.even_add_odd
    (f := fun n : ℕ => (1/2:ℝ)^n*alternatingReward n) he ho)

theorem alternating_return_worn :
    HasSum (fun n : ℕ => (1/2:ℝ)^n*alternatingReward (n+1)) (2/3) := by
  have he : HasSum (fun n : ℕ => (1/2:ℝ)^(2*n)*alternatingReward (2*n+1)) 0 := by
    convert hasSum_zero using 1
    ext n; simp [alternatingReward]
  have ho : HasSum (fun n : ℕ => (1/2:ℝ)^(2*n+1)*alternatingReward (2*n+1+1)) (2/3) := by
    have hh := (hasSum_geometric_of_abs_lt_one
      (by norm_num : |(1/4:ℝ)|<1)).mul_left (1/2:ℝ)
    norm_num at hh
    convert hh using 1
    ext n
    have hp : (2*n+1+1)%2=0 := by omega
    simp [alternatingReward,hp,pow_add,pow_mul]
    norm_num
    ring
  simpa only [zero_add] using (HasSum.even_add_odd
    (f := fun n : ℕ => (1/2:ℝ)^n*alternatingReward (n+1)) he ho)

theorem optimal_half_backup_unique (v : ℝ) :
    max (1+(1/2)*v) (2+(1/2)*v)=v ↔ v=4 := by
  rw [max_eq_right (by linarith)]
  constructor <;> intro h <;> linarith

theorem half_iteration_error (n : ℕ) :
    |halfValueIteration n-4|=4*(1/2:ℝ)^n ∧
    |halfValueIteration (n+1)-4|=(1/2)*|halfValueIteration n-4| := by
  have hn : 0≤(1/2:ℝ)^n := pow_nonneg (by norm_num) n
  have herror : ∀ n : ℕ,|halfValueIteration n-4|=4*(1/2:ℝ)^n := by
    intro m
    rw [half_value_iteration_formula,abs_of_nonpos]
    · ring
    · nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤1/2) m]
  rw [herror,herror]
  constructor
  · rfl
  · ring

theorem correlation_arbitrary_window (x : Fin 4 → ℝ) :
    correlationMatrix.mulVec x=![x 0-x 1,x 1-x 2,x 2-x 3] := by
  ext i
  fin_cases i <;> simp [correlationMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;> ring

theorem stationary_count_budget_distinct : (100/41:ℝ)≠1/2 := by norm_num

theorem ready_equilibrium (x : ℝ) : (1/2)*x+1=x ↔ x=2 := by
  constructor <;> intro h <;> linarith

theorem ready_rate_initial : (3*Real.exp (-2*(0:ℝ)))=3 ∧
    (-2*(3*Real.exp (-2*(0:ℝ))))=-6 ∧ (3:ℝ)≠-6 := by norm_num

theorem ready_rate_local_approximation (t : ℝ) :
    (fun s : ℝ => 3*Real.exp (-2*s)-3*Real.exp (-2*t)-
      (s-t)*(-2*(3*Real.exp (-2*t))))=o[𝓝 t] (fun s : ℝ => s-t) := by
  simpa only [smul_eq_mul] using
    (SafeLearning.CompleteAppliedElementary.d_ready_derivative t).isLittleO

theorem ready_quadratic_value : (1:ℝ)^2+(-2)^2=5 ∧ (1:ℝ)^2+2*(-2)^2=9 := by norm_num

theorem scalar_residual_bound (g : ℝ → ℝ) (L : ℝ)
    (h : SafeLearning.CompleteAppliedElementary.IsLipschitzBound g L) :
    SafeLearning.CompleteAppliedElementary.IsLipschitzBound (fun x => x+g x) (1+L) := by
  intro x y
  have he : x+g x-(y+g y)=(x-y)+(g x-g y) := by ring
  rw [he]
  calc
    _≤|x-y|+|g x-g y| := abs_add_le _ _
    _≤|x-y|+L*|x-y| := add_le_add_right (h x y) _
    _=(1+L)*|x-y| := by ring

end SafeLearning.CompleteAppliedExerciseModels
