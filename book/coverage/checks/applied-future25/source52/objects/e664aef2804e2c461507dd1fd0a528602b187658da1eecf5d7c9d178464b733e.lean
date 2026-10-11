import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SafeLearning.CompleteFoundationsNonnegativeSeriesModels

def actualPartialSums (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, a n

theorem actual_nonnegative_partial_sums_are_monotone (a : ℕ → ℝ)
    (ha : ∀n,0≤a n) : Monotone (actualPartialSums a) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [actualPartialSums,Finset.sum_range_succ]
  exact le_add_of_nonneg_right (ha n)

theorem actual_nonnegative_series_converges_iff_its_partial_sums_are_bounded
    (a : ℕ → ℝ) (ha : ∀n,0≤a n) :
    (∃s:ℝ,Tendsto (actualPartialSums a) atTop (𝓝 s)) ↔
      BddAbove (range (actualPartialSums a)) := by
  constructor
  · rintro ⟨s,hs⟩
    refine ⟨s,?_⟩
    rintro value ⟨n,rfl⟩
    exact ge_of_tendsto hs (eventually_atTop.mpr ⟨n,fun k hk =>
      actual_nonnegative_partial_sums_are_monotone a ha hk⟩)
  · intro hb
    exact ⟨sSup (range (actualPartialSums a)),
      tendsto_atTop_ciSup (actual_nonnegative_partial_sums_are_monotone a ha) hb⟩

theorem actual_nonnegative_natural_series_convergence_is_genuine_summability
    (a : ℕ → ℝ) (ha : ∀n,0≤a n) :
    (∃s:ℝ,Tendsto (actualPartialSums a) atTop (𝓝 s)) ↔ Summable a := by
  constructor
  · rintro ⟨s,hs⟩
    exact ⟨s,(hasSum_iff_tendsto_nat_of_nonneg ha s).mpr hs⟩
  · intro hs
    exact ⟨∑'n,a n,hs.hasSum.tendsto_sum_nat⟩

theorem actual_nonnegative_comparison_implies_series_convergence
    (a b : ℕ→ℝ) (ha : ∀n,0≤a n) (hab : ∀n,a n≤b n)
    (hb : Summable b) : Summable a := hb.of_nonneg_of_le ha hab

theorem actual_absolute_convergence_implies_natural_partial_sum_convergence
    (a : ℕ→ℝ) (ha : Summable (fun n=>|a n|)) :
    Summable a ∧ Tendsto (actualPartialSums a) atTop (𝓝 (∑'n,a n)) := by
  have hs : Summable a := Summable.of_norm (by simpa only [Real.norm_eq_abs] using ha)
  exact ⟨hs,hs.hasSum.tendsto_sum_nat⟩

/-- This uses only convergence of the ordinary natural-order sums, not unconditional summability. -/
theorem actual_convergent_natural_partial_sums_force_the_actual_terms_to_zero
    (a : ℕ→ℝ) (s : ℝ) (hs : Tendsto (actualPartialSums a) atTop (𝓝 s)) :
    Tendsto a atTop (𝓝 0) := by
  have hshift : Tendsto (fun n=>actualPartialSums a (n+1)) atTop (𝓝 s) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have h := hshift.sub hs
  simpa only [actualPartialSums,Finset.sum_range_succ,add_sub_cancel_left,sub_self] using h

def actualHarmonicPartialSums (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, 1/((n:ℝ)+1)

theorem actual_harmonic_terms_tend_to_zero_but_their_partial_sums_tend_to_infinity :
    Tendsto (fun n:ℕ=>1/((n:ℝ)+1)) atTop (𝓝 0) ∧
      Tendsto actualHarmonicPartialSums atTop atTop := by
  exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Real.tendsto_sum_range_one_div_nat_succ_atTop⟩

def actualHarmonicBlock (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range m, 1/(((m+k:ℕ):ℝ)+1)

theorem actual_each_positive_length_harmonic_block_has_at_least_half
    (m : ℕ) (hm : 0 < m) : (1/2:ℝ)≤actualHarmonicBlock m := by
  have hmreal : (0:ℝ) < m := by exact_mod_cast hm
  have heach : ∀k∈Finset.range m, 1/((2*m:ℕ):ℝ)≤1/(((m+k:ℕ):ℝ)+1) := by
    intro k hk
    have hkm : k < m := Finset.mem_range.mp hk
    have hden : (0:ℝ)<((m+k:ℕ):ℝ)+1 := by positivity
    apply (div_le_div_iff₀ (by positivity : (0:ℝ)<((2*m:ℕ):ℝ)) hden).mpr
    push_cast
    simp only [one_mul]
    exact_mod_cast (show m+k+1≤2*m by omega)
  have h := Finset.sum_le_sum heach
  have heq : (∑ _k ∈ Finset.range m, 1/((2*m:ℕ):ℝ))=(1/2:ℝ) := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    push_cast
    field_simp [hmreal.ne']
  rw [heq] at h
  exact h

theorem actual_power_two_block_has_the_literal_half_lower_bound (j : ℕ) :
    (1/2:ℝ)≤∑ k∈Finset.range (2^j),1/(((2^j+k:ℕ):ℝ)+1) := by
  exact actual_each_positive_length_harmonic_block_has_at_least_half _ (by positivity)

theorem actual_adjacent_harmonic_blocks_split_the_actual_partial_sum (m : ℕ) :
    actualHarmonicPartialSums (2*m)=actualHarmonicPartialSums m+actualHarmonicBlock m := by
  rw [show 2*m=m+m by omega]
  simp only [actualHarmonicPartialSums,actualHarmonicBlock,Finset.sum_range_add,Nat.cast_add]

theorem actual_dyadic_partial_sums_have_the_unbounded_block_lower_bound (j : ℕ) :
    1+(j:ℝ)/2≤actualHarmonicPartialSums (2^j) := by
  induction j with
  | zero => norm_num [actualHarmonicPartialSums,Finset.sum_range_succ]
  | succ j ih =>
    have hb := actual_each_positive_length_harmonic_block_has_at_least_half (2^j) (by positivity)
    rw [pow_succ,mul_comm (2^j) 2,actual_adjacent_harmonic_blocks_split_the_actual_partial_sum]
    push_cast
    linarith

def actualTelescopingMajorant (n : ℕ) : ℝ := 1/(((n:ℝ)+1)*((n:ℝ)+2))

theorem actual_reciprocal_product_telescopes_at_every_horizon (N : ℕ) :
    (∑n∈Finset.range N,actualTelescopingMajorant n)=1-1/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    dsimp [actualTelescopingMajorant]
    push_cast
    field_simp
    ring

theorem actual_reciprocal_product_series_has_sum_one : HasSum actualTelescopingMajorant 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun n=>by dsimp [actualTelescopingMajorant];positivity) 1).mpr
  have ht : Tendsto (fun N:ℕ=>1-1/((N:ℝ)+1)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  simpa only [actual_reciprocal_product_telescopes_at_every_horizon] using ht

theorem actual_square_reciprocal_tail_is_bounded_by_the_telescoping_majorant (n : ℕ) :
    (0:ℝ)≤1/((n:ℝ)+2)^2 ∧ 1/((n:ℝ)+2)^2≤actualTelescopingMajorant n := by
  constructor
  · positivity
  · unfold actualTelescopingMajorant
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

theorem actual_square_reciprocal_series_converges_and_has_sum_at_most_two :
    Summable (fun n:ℕ=>1/((n:ℝ)+1)^2) ∧
      (∑'n:ℕ,1/((n:ℝ)+1)^2)≤2 := by
  have ht : Summable (fun n:ℕ=>1/((n:ℝ)+2)^2) :=
    actual_reciprocal_product_series_has_sum_one.summable.of_nonneg_of_le
      (fun n=>(actual_square_reciprocal_tail_is_bounded_by_the_telescoping_majorant n).1)
      (fun n=>(actual_square_reciprocal_tail_is_bounded_by_the_telescoping_majorant n).2)
  have hs : Summable (fun n:ℕ=>1/((n:ℝ)+1)^2) := by
    have hshift : Summable (fun n:ℕ=>1/(((n+1:ℕ):ℝ)+1)^2) := by
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using ht
    exact (summable_nat_add_iff 1).mp hshift
  have hsum := ht.tsum_le_tsum
    (fun n=>(actual_square_reciprocal_tail_is_bounded_by_the_telescoping_majorant n).2)
    actual_reciprocal_product_series_has_sum_one.summable
  rw [actual_reciprocal_product_series_has_sum_one.tsum_eq] at hsum
  have hsplit := hs.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one,Nat.cast_zero,zero_add,one_pow,div_one] at hsplit
  have heq : (∑'n:ℕ,1/(((n+1:ℕ):ℝ)+1)^2)=∑'n:ℕ,1/((n:ℝ)+2)^2 := by
    apply tsum_congr;intro n;push_cast;congr 1;ring
  rw [heq] at hsplit
  exact ⟨hs,by linarith⟩

end SafeLearning.CompleteFoundationsNonnegativeSeriesModels
