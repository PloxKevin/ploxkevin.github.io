import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace SafeLearning.CompleteFoundationsSupremumExamples

theorem actual_bounded_exponential_modulus_is_strictly_below_one
    (r : ℝ) (hr : 0 ≤ r) : 0 ≤ 1-Real.exp (-r) ∧ 1-Real.exp (-r)<1 := by
  constructor
  · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
    linarith
  · linarith [Real.exp_pos (-r)]

theorem actual_bounded_exponential_modulus_has_supremum_one_but_no_attainer :
    IsLUB ((fun r : ℝ => 1-Real.exp (-r)) '' Ici 0) 1 ∧
      ¬∃ r : ℝ, 0 ≤ r ∧ 1-Real.exp (-r)=1 := by
  have hlim : Tendsto (fun n : ℕ => 1-Real.exp (-(n:ℝ))) atTop (𝓝 1) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)
    simpa using tendsto_const_nhds.sub h
  constructor
  · constructor
    · rintro z ⟨r,hr,rfl⟩
      exact (actual_bounded_exponential_modulus_is_strictly_below_one r hr).2.le
    · intro u hu
      exact le_of_tendsto hlim (Eventually.of_forall (fun n =>
        hu (mem_image_of_mem _ (show (n:ℝ)∈Ici 0 from (show 0 ≤ (n:ℝ) from Nat.cast_nonneg n)))))
  · rintro ⟨r,hr,he⟩
    exact (ne_of_lt (actual_bounded_exponential_modulus_is_strictly_below_one r hr).2) he

theorem actual_negative_square_exponential_has_an_attained_maximum_one :
    IsGreatest (range (fun x : ℝ => Real.exp (-(x^2)))) 1 := by
  constructor
  · exact ⟨0,by simp⟩
  · rintro z ⟨x,rfl⟩
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg x))

def sineSecants : Set ℝ := {r | ∃ x y : ℝ, x≠y ∧ r=|Real.sin x-Real.sin y|/|x-y|}

theorem actual_every_distinct_sine_secant_is_strictly_below_one
    (x y : ℝ) (hxy : x≠y) : |Real.sin x-Real.sin y|/|x-y|<1 := by
  have hn : (x-y)/2≠0 := div_ne_zero (sub_ne_zero.mpr hxy) (by norm_num)
  have hs := Real.abs_sin_lt_abs hn
  have hc := Real.abs_cos_le_one ((x+y)/2)
  have hdiff : |Real.sin x-Real.sin y| < |x-y| := by
    calc
      |Real.sin x-Real.sin y|=2*|Real.sin ((x-y)/2)|*|Real.cos ((x+y)/2)| := by
        rw [Real.sin_sub_sin,abs_mul,abs_mul]
        norm_num
      _ ≤ 2*|Real.sin ((x-y)/2)| := by
        nlinarith [abs_nonneg (Real.sin ((x-y)/2))]
      _ < 2*|(x-y)/2| := by linarith
      _ = |x-y| := by rw [abs_div];norm_num
  exact (div_lt_one (abs_pos.mpr (sub_ne_zero.mpr hxy))).mpr hdiff

theorem actual_sine_secants_approach_one_at_zero :
    Tendsto (fun x : ℝ => |Real.sin x|/|x|) (𝓝[≠] 0) (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => Real.sin x/x) (𝓝[≠] 0) (𝓝 1) := by
    simpa [Real.cos_zero,Real.sin_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  simpa only [abs_div,abs_one] using h.abs

theorem actual_sine_secant_set_has_supremum_one_and_never_attains_it :
    IsLUB sineSecants 1 ∧ 1∉sineSecants := by
  constructor
  · constructor
    · rintro r ⟨x,y,hxy,rfl⟩
      exact (actual_every_distinct_sine_secant_is_strictly_below_one x y hxy).le
    · intro u hu
      apply le_of_tendsto actual_sine_secants_approach_one_at_zero
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hn : x≠0 := hx
      apply hu
      refine ⟨x,0,hn,?_⟩
      simp
  · rintro ⟨x,y,hxy,he⟩
    have h := actual_every_distinct_sine_secant_is_strictly_below_one x y hxy
    linarith

theorem actual_pointwise_cancellation_supremum_is_strictly_less_than_separate_suprema :
    sSup ((fun x : ℝ => x+(-x)) '' Icc 0 1)=0 ∧
      sSup (Icc (0:ℝ) 1)=1 ∧ sSup ((fun x : ℝ => -x) '' Icc 0 1)=0 ∧
      (0:ℝ)<1+0 := by
  have hi : IsGreatest (Icc (0:ℝ) 1) 1 := ⟨by norm_num,fun _ h => h.2⟩
  have hn : IsGreatest ((fun x : ℝ => -x) '' Icc 0 1) 0 := by
    refine ⟨⟨0,by norm_num,by norm_num⟩,?_⟩
    rintro z ⟨x,hx,rfl⟩
    linarith [hx.1]
  refine ⟨?_,hi.isLUB.csSup_eq ⟨0,by norm_num⟩,
    hn.isLUB.csSup_eq ⟨0,⟨0,by norm_num,by norm_num⟩⟩,by norm_num⟩
  have he : ((fun x : ℝ => x+(-x)) '' Icc 0 1)={0} := by
    ext z
    simp only [add_neg_cancel,mem_image,mem_Icc,mem_singleton_iff]
    constructor
    · rintro ⟨x,hx,h⟩;exact h.symm
    · intro h;exact ⟨0,by norm_num,by simpa using h.symm⟩
  rw [he,csSup_singleton]

def binaryPayoff (x y : Fin 2) : ℝ := ((x.val:ℝ)-(y.val:ℝ))^2

theorem actual_binary_quadratic_payoff_has_each_row_and_column_range_zero_one :
    (∀ x : Fin 2, range (binaryPayoff x)={0,1}) ∧
      ∀ y : Fin 2, range (fun x => binaryPayoff x y)={0,1} := by
  constructor <;> intro i <;> fin_cases i <;> ext z <;>
    norm_num [binaryPayoff,Fin.exists_fin_two, eq_comm, or_comm]

theorem actual_binary_quadratic_source_game_has_a_strict_max_min_gap :
    sSup (range (fun y : Fin 2 => sInf (range (fun x => binaryPayoff x y))))=0 ∧
      sInf (range (fun x : Fin 2 => sSup (range (binaryPayoff x))))=1 := by
  have hrow : ∀ x : Fin 2, sSup (range (binaryPayoff x))=1 := by
    intro x
    rw [actual_binary_quadratic_payoff_has_each_row_and_column_range_zero_one.1 x,
      csSup_pair]
    norm_num
  have hcol : ∀ y : Fin 2, sInf (range (fun x => binaryPayoff x y))=0 := by
    intro y
    rw [actual_binary_quadratic_payoff_has_each_row_and_column_range_zero_one.2 y,
      csInf_pair]
    norm_num
  simp only [hcol,hrow]
  simp

end SafeLearning.CompleteFoundationsSupremumExamples
