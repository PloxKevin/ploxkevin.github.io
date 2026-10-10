import SafeLearning.CompleteFoundationsRatesConsequences
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsRatesDomain
open Set Filter Asymptotics
open scoped Topology BigOperators
open SafeLearning.CompleteFoundationsRatesConsequences

theorem actual_source_regret_is_little_o_without_initial_premise (R : ℕ→ℝ)
    (hR : ∀ n,1≤n→0≤R n ∧ R n≤ sourceRate n) :
    IsLittleO atTop R (fun n=>(n:ℝ)) := by
  apply isLittleO_of_tendsto' ?_ (actual_nonnegative_source_average_regret_tends_to_zero R hR)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  intro hz
  have hp : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  exact False.elim (hp.ne' hz)

def cumulativeRegret (comparator : ℝ) (observations : ℕ→ℝ) (budget : ℕ) : ℝ :=
  ∑ index∈Finset.range budget,(comparator-observations index)

def simpleRegret (comparator recommendation : ℝ) : ℝ := comparator-recommendation

theorem actual_global_maximizer_comparator_gives_nonnegative_regret
    (comparator : ℝ) (observations : ℕ→ℝ) (budget : ℕ)
    (hmax : ∀ index,observations index≤comparator) :
    0≤cumulativeRegret comparator observations budget := by
  unfold cumulativeRegret
  exact Finset.sum_nonneg (fun index _=>sub_nonneg.mpr (hmax index))

theorem actual_best_query_regret_le_average (comparator : ℝ) (observations : ℕ→ℝ)
    (budget : ℕ) (hb : 0<budget) :
    ∃ index<budget,simpleRegret comparator (observations index)≤
      cumulativeRegret comparator observations budget/budget := by
  classical
  by_contra h
  push Not at h
  have hsum : cumulativeRegret comparator observations budget<
      ∑ index∈Finset.range budget,simpleRegret comparator (observations index) := by
    have he : (∑ _index∈Finset.range budget,
      cumulativeRegret comparator observations budget/budget)=
      cumulativeRegret comparator observations budget := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      field_simp
    rw [←he]
    apply Finset.sum_lt_sum_of_nonempty
    · exact Finset.nonempty_range_iff.mpr (by omega)
    · intro index hi
      exact h index (Finset.mem_range.mp hi)
  change cumulativeRegret comparator observations budget<cumulativeRegret comparator observations budget at hsum
  exact lt_irrefl _ hsum
end SafeLearning.CompleteFoundationsRatesDomain
