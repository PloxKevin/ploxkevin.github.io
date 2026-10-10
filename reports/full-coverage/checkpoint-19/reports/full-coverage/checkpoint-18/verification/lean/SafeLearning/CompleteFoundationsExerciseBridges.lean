import SafeLearning.PrimersFoundations
import SafeLearning.CompleteFoundationsSeries
import SafeLearning.CompleteFoundationsLogic
import SafeLearning.CompleteFoundationsTeaching

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsExerciseBridges

theorem grow_image_monotone {X : Type*} [DecidableEq X] (F : X → X) :
    Monotone (fun S : Finset X => S ∪ S.image F) := by
  intro A B hAB
  exact Finset.union_subset_union hAB (Finset.image_subset_image hAB)

theorem reach_five_strict_increases :
    ({0} : Finset (Fin 5)) ⊂ {0,1} ∧ ({0,1} : Finset (Fin 5)) ⊂ {0,1,2} := by decide

theorem reach_five_unreachable (n : ℕ) :
    (3 : Fin 5) ∉ SafeLearning.PrimersFoundations.reachFive^[n] {0} ∧
      (4 : Fin 5) ∉ SafeLearning.PrimersFoundations.reachFive^[n] {0} := by
  have hinv : ∀ n, SafeLearning.PrimersFoundations.reachFive^[n] {0} ⊆ ({0,1,2} : Finset (Fin 5)) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hm := grow_image_monotone SafeLearning.PrimersFoundations.reachFiveF ih
      change SafeLearning.PrimersFoundations.reachFive
        (SafeLearning.PrimersFoundations.reachFive^[n] {0}) ⊆
        SafeLearning.PrimersFoundations.reachFive {0,1,2} at hm
      rw [SafeLearning.PrimersFoundations.reachFive_iterates.2.2] at hm
      exact hm
  constructor <;> intro h <;> have hh := hinv n h <;> norm_num at hh

theorem half_shift_contraction (x y : ℝ) :
    |(x/2+1)-(y/2+1)|=|x-y|/2 := by
  have h : (x/2+1)-(y/2+1)=(x-y)/2 := by ring
  rw [h,abs_div]; norm_num

theorem closed_intervals_for_contraction :
    IsClosed (Icc (0 : ℝ) 1) ∧ IsClosed (Icc (-1 : ℝ) 1) :=
  ⟨isClosed_Icc,isClosed_Icc⟩

theorem half_shift_fixed_point (x : ℝ) : x/2+1=x ↔ x=2 := by
  constructor <;> intro h <;> linarith

theorem negation_selfmap (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    -x ∈ Icc (-1 : ℝ) 1 := by
  constructor <;> linarith [hx.1,hx.2]

theorem negation_fixed_point (x : ℝ) : -x=x ↔ x=0 := by
  constructor <;> intro h <;> linarith

theorem negation_iteration (n : ℕ) : (fun x : ℝ => -x)^[n] 1=(-1)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ]; ring

theorem subtype_contraction_uniqueness (X : Set ℝ) (g : X → X)
    (hg : ∀ x y : X, |(g x : ℝ)-(g y : ℝ)| ≤ |(x : ℝ)-(y : ℝ)|/3)
    (x y : X) (hx : g x=x) (hy : g y=y) : x=y := by
  have h := hg x y
  rw [hx,hy] at h
  have hzero : |(x : ℝ)-(y : ℝ)|=0 := by
    have hp := abs_nonneg ((x : ℝ)-(y : ℝ)); linarith
  apply Subtype.ext
  exact sub_eq_zero.mp (abs_eq_zero.mp hzero)

theorem half_discount_uniform_minimal (T : ℕ) :
    (∀ r : ℕ → ℝ, (∀ n, |r n| ≤ 2) →
      |∑' n : ℕ, (1/2 : ℝ)^(n+T)*r (n+T)| ≤ 1/100) ↔ 9 ≤ T := by
  constructor
  · intro h
    have hh := h (fun _ => 2) (by intro n; norm_num)
    rw [SafeLearning.CompleteFoundationsSeries.constant_discounted_tail
      (1/2) 2 T (by norm_num) (by norm_num)] at hh
    have hpos : 0 ≤ 2*(1/2 : ℝ)^T/(1-1/2) := by positivity
    rw [abs_of_nonneg hpos] at hh
    have he : 2*(1/2 : ℝ)^T/(1-1/2)=4*(1/2 : ℝ)^T := by ring
    rw [he] at hh
    exact SafeLearning.CompleteFoundationsSeries.half_discount_minimal_budget T |>.mp hh
  · intro h r hr
    have hh := SafeLearning.CompleteFoundationsSeries.discounted_tail_bound r (1/2) 2 T
      (by norm_num) (by norm_num) hr
    have he : 2*(1/2 : ℝ)^T/(1-1/2)=4*(1/2 : ℝ)^T := by ring
    rw [he] at hh
    exact hh.trans (SafeLearning.CompleteFoundationsSeries.half_discount_minimal_budget T |>.mpr h)

theorem constant_discounted_return_attains :
    (∑' n : ℕ, (1/2 : ℝ)^n*2)=4 := by
  have h := SafeLearning.CompleteFoundationsSeries.constant_discounted_tail (1/2) 2 0
    (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem reciprocal_decimal_enclosure :
    |(3 : ℝ)/31-9677/100000|<1/200000 := by norm_num

theorem modeled_energy_conclusions {E : Type*} [NormedAddCommGroup E]
    (V : ℕ → ℝ) (x : ℕ → E) (hV₀ : V 0=3) (hV : ∀ n, 0≤V n)
    (hstep : ∀ n, V (n+1)-V n≤ -‖x n‖^2/2) :
    Tendsto x atTop (𝓝 0) ∧ {n | 1/5≤‖x n‖}.Finite ∧
      {n | 1/5≤‖x n‖}.ncard≤150 ∧
        ∃ N : ℕ, ∀ n ≥ N, ‖x n‖<1/5 := by
  have hb : ∀ T, (∑ n ∈ Finset.range T, ‖x n‖^2)≤6 := by
    intro T
    have hh := SafeLearning.CompleteFoundationsLogic.telescoping_energy_budget V
      (fun n => ‖x n‖^2) hV (fun n => sq_nonneg _) hstep T
    rw [hV₀] at hh
    norm_num at hh
    exact hh
  have hcount := SafeLearning.CompleteFoundationsTeaching.all_time_excursion_card
    (fun n => ‖x n‖^2) (fun n => sq_nonneg _) hb
  have heq : {n | (1/25 : ℝ)≤‖x n‖^2}={n | (1/5 : ℝ)≤‖x n‖} := by
    ext n
    simp only [mem_setOf_eq]
    constructor <;> intro h <;> nlinarith [norm_nonneg (x n)]
  rw [heq] at hcount
  refine ⟨SafeLearning.CompleteFoundationsLogic.telescoping_state_convergence V x hV hstep,
    hcount.1,hcount.2,?_⟩
  obtain ⟨N,hN⟩ := hcount.1.bddAbove
  refine ⟨N+1,?_⟩
  intro n hn
  by_contra h
  have hh := hN (show n ∈ {n | (1/5 : ℝ)≤‖x n‖} from le_of_not_gt h)
  omega

theorem arbitrarily_late_modeled_excursion (N : ℕ) :
    ∃ V x : ℕ → ℝ, V 0=3 ∧ (∀ n, 0 ≤ V n) ∧
      (∀ n, V (n+1)-V n ≤ -|x n|^2/2) ∧
      x N=1/5 ∧ (∀ n, n≠N → x n=0) := by
  let V : ℕ → ℝ := fun n => if n≤N then 3 else 3-1/50
  let x : ℕ → ℝ := fun n => if n=N then 1/5 else 0
  refine ⟨V,x,?_,?_,?_,?_,?_⟩
  · simp [V]
  · intro n; dsimp [V]; split_ifs <;> norm_num
  · intro n
    by_cases h₁ : n=N
    · subst n
      have h₂ : ¬N+1≤N := by omega
      norm_num [V,x,h₂]
    by_cases h₂ : n<N
    · have h₃ : n≤N := by omega
      have h₄ : n+1≤N := by omega
      norm_num [V,x,h₁,h₃,h₄]
    · have h₃ : ¬n≤N := by omega
      have h₄ : ¬n+1≤N := by omega
      norm_num [V,x,h₁,h₃,h₄]
  · simp [x]
  · intro n hn; simp [x,hn]

end SafeLearning.CompleteFoundationsExerciseBridges
