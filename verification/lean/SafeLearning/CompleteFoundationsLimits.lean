import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsLimits

theorem half_open_interval_extrema :
    IsGLB (Ioc (-2 : ℝ) 3) (-2) ∧ IsLUB (Ioc (-2 : ℝ) 3) 3 ∧
    (-2 : ℝ) ∉ Ioc (-2 : ℝ) 3 ∧ (3 : ℝ) ∈ Ioc (-2 : ℝ) 3 := by
  exact ⟨isGLB_Ioc (by norm_num),isLUB_Ioc (by norm_num),by norm_num,by norm_num⟩

theorem approaching_one_extrema :
    IsGLB (range (fun n : ℕ => 1-1/((n : ℝ)+1))) 0 ∧
    IsLUB (range (fun n : ℕ => 1-1/((n : ℝ)+1))) 1 ∧
    (0 : ℝ) ∈ range (fun n : ℕ => 1-1/((n : ℝ)+1)) ∧
    (1 : ℝ) ∉ range (fun n : ℕ => 1-1/((n : ℝ)+1)) := by
  have hlo (n : ℕ) : 0 ≤ 1-1/((n : ℝ)+1) := by
    have hn : (1 : ℝ) ≤ n+1 := by exact_mod_cast Nat.le_add_left 1 n
    have hh : 1/((n : ℝ)+1) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hhi (n : ℕ) : 1-1/((n : ℝ)+1) < 1 := by
    have hh : 0 < 1/((n : ℝ)+1) := by positivity
    linarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨0,by norm_num⟩,?_⟩
  · rintro x ⟨n,rfl⟩; exact hlo n
  · intro z hz; exact hz ⟨0,by norm_num⟩
  · rintro x ⟨n,rfl⟩; exact (hhi n).le
  · intro z hz
    by_contra h
    have hgap : 0 < 1-z := by linarith
    obtain ⟨n,hn⟩ := exists_nat_one_div_lt hgap
    have hh := hz (mem_range_self n)
    linarith
  · rintro ⟨n,hn⟩; have hh := hhi n; linarith

theorem open_interval_sup_and_no_argmax :
    IsLUB (Ioo (0 : ℝ) 1) 1 ∧
    (¬ ∃ x ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Ioo (0 : ℝ) 1, y ≤ x) ∧
    (99/100 : ℝ) ∈ Ioo (0 : ℝ) 1 ∧ (1 : ℝ)-1/100 ≤ 99/100 := by
  refine ⟨isLUB_Ioo (by norm_num),?_,by norm_num,by norm_num⟩
  rintro ⟨x,hx,hmax⟩
  have hm : (x+1)/2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hh := hmax ((x+1)/2) hm
  linarith [hx.2]

theorem square_closed_interval_argmax (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    x^2 ≤ 1 ∧ (x^2=1 ↔ x= -1 ∨ x=1) := by
  constructor
  · nlinarith [hx.1,hx.2]
  · constructor
    · intro h; have hh := sq_eq_one_iff.mp h; tauto
    · rintro (rfl | rfl) <;> norm_num

theorem half_open_square_no_minimum :
    ¬ ∃ x ∈ Ioc (0 : ℝ) 1, ∀ y ∈ Ioc (0 : ℝ) 1, x^2 ≤ y^2 := by
  rintro ⟨x,hx,hmin⟩
  have hm : x/2 ∈ Ioc (0 : ℝ) 1 := by constructor <;> linarith [hx.1,hx.2]
  have hh := hmin (x/2) hm
  nlinarith [sq_pos_of_pos hx.1]

theorem square_unique_minimum_on_real (x : ℝ) : 0 ≤ x^2 ∧ (x^2=0 ↔ x=0) := by
  exact ⟨sq_nonneg x,sq_eq_zero_iff⟩

theorem half_open_interval_topology :
    ¬ IsOpen (Ioc (-1 : ℝ) 1) ∧ ¬ IsClosed (Ioc (-1 : ℝ) 1) ∧
    Bornology.IsBounded (Ioc (-1 : ℝ) 1) ∧ ¬ IsCompact (Ioc (-1 : ℝ) 1) ∧
    IsCompact ({0,1} : Set ℝ) := by
  have hInt : interior (Ioc (-1 : ℝ) 1)=Ioo (-1 : ℝ) 1 := by simp
  have hCl : closure (Ioc (-1 : ℝ) 1)=Icc (-1 : ℝ) 1 := by norm_num [closure_Ioc]
  have hnotopen : ¬ IsOpen (Ioc (-1 : ℝ) 1) := by
    intro h
    have he := h.interior_eq
    rw [hInt] at he
    have hh : (1 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by rw [he]; norm_num
    norm_num at hh
  have hnotclosed : ¬ IsClosed (Ioc (-1 : ℝ) 1) := by
    intro h
    have he := h.closure_eq
    rw [hCl] at he
    have hh : (-1 : ℝ) ∈ Ioc (-1 : ℝ) 1 := by rw [← he]; norm_num
    norm_num at hh
  refine ⟨hnotopen,hnotclosed,?_,fun h => hnotclosed h.isClosed,?_⟩
  · exact (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)).isBounded.subset Ioc_subset_Icc_self
  · exact (Set.toFinite _).isCompact

theorem reciprocal_sequence_limit :
    Tendsto (fun n : ℕ => (3 : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) := by
  have hh : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  simpa only [div_eq_mul_inv,mul_zero] using hh.const_mul 3

theorem affine_error_bound_limit (q b a : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    Tendsto (fun n : ℕ => b+q^n*(a-b)) atTop (𝓝 b) := by
  have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).mul_const (a-b)
  simpa using tendsto_const_nhds.add hh

theorem polynomial_ratio_limit :
    Tendsto (fun n : ℕ => (2*((n : ℝ)+1)^2+3*((n : ℝ)+1)+1)/((n : ℝ)+1)^2)
      atTop (𝓝 2) := by
  have hi : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hh := ((tendsto_const_nhds (x := (2 : ℝ))).add (hi.const_mul 3)).add (hi.pow 2)
  convert hh using 1
  · ext n; field_simp
  · norm_num

theorem average_log_sqrt_limit :
    Tendsto (fun t : ℝ => 5*Real.log t/Real.sqrt t) atTop (𝓝 0) := by
  have hh := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).tendsto_div_nhds_zero
  have he : (fun t : ℝ => Real.log t/Real.sqrt t)=(fun t : ℝ => Real.log t/t^(1/2 : ℝ)) := by
    ext t; rw [Real.sqrt_eq_rpow]
  rw [← he] at hh
  simpa [mul_div_assoc] using hh.const_mul 5

theorem bounded_average_regret_converges (R : ℝ → ℝ)
    (h : ∀ᶠ t in atTop, 0 ≤ R t/t ∧ R t/t ≤ 5*Real.log t/Real.sqrt t) :
    Tendsto (fun t => R t/t) atTop (𝓝 0) := by
  exact squeeze_zero' (h.mono fun _ hh => hh.1) (h.mono fun _ hh => hh.2) average_log_sqrt_limit

theorem log_sqrt_product_counterexample (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t*Real.sqrt t=t := Real.mul_self_sqrt ht

theorem sqrt_sublinear :
    Tendsto (fun t : ℝ => Real.sqrt t/t) atTop (𝓝 0) := by
  have hh : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hs := Real.mul_self_sqrt ht.le
  have hn : Real.sqrt t ≠ 0 := by positivity
  field_simp; nlinarith

end SafeLearning.CompleteFoundationsLimits
