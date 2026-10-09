import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsSequences

theorem even_indices_atTop : Tendsto (fun n : ℕ => 2*n) atTop atTop :=
  tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id

theorem odd_indices_atTop : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
  tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id

theorem reciprocal_tail :
    Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0) := by
  simpa only [one_div,Function.comp_def] using
    tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)

theorem alternating_limits (a b : ℕ → ℝ)
    (hbound : ∀ n, -2 ≤ a n ∧ a n ≤ 2)
    (hsandwich : ∀ n, -1-b n ≤ a n ∧ a n ≤ 1+b n)
    (hb : Tendsto b atTop (𝓝 0))
    (heven : Tendsto (fun n => a (2*n)) atTop (𝓝 1))
    (hodd : Tendsto (fun n => a (2*n+1)) atTop (𝓝 (-1))) :
    limsup a atTop=1 ∧ liminf a atTop= -1 ∧
      ¬ ∃ l : ℝ, Tendsto a atTop (𝓝 l) := by
  have hu : IsBoundedUnder (· ≤ ·) atTop a :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n => (hbound n).2)
  have hl : IsBoundedUnder (· ≥ ·) atTop a :=
    isBoundedUnder_of_eventually_ge (Eventually.of_forall fun n => (hbound n).1)
  have hup : Tendsto (fun n => 1+b n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hb
  have hlo : Tendsto (fun n => -1-b n) atTop (𝓝 (-1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hb
  have hsupu : limsup a atTop ≤ 1 := by
    calc
      limsup a atTop ≤ limsup (fun n => 1+b n) atTop :=
        limsup_le_limsup (Eventually.of_forall fun n => (hsandwich n).2)
          hl.isCoboundedUnder_le hup.isBoundedUnder_le
      _ = 1 := hup.limsup_eq
  have hinfl : -1 ≤ liminf a atTop := by
    calc
      -1 = liminf (fun n => -1-b n) atTop := hlo.liminf_eq.symm
      _ ≤ liminf a atTop :=
        liminf_le_liminf (Eventually.of_forall fun n => (hsandwich n).1)
          hlo.isBoundedUnder_ge hu.isCoboundedUnder_ge
  have hsup : limsup a atTop=1 := le_antisymm hsupu
    ((heven.mapClusterPt.of_comp even_indices_atTop).le_limsup hu)
  have hinf : liminf a atTop= -1 := le_antisymm
    ((hodd.mapClusterPt.of_comp odd_indices_atTop).liminf_le hl) hinfl
  refine ⟨hsup,hinf,?_⟩
  rintro ⟨l,ht⟩
  have h₁ := ht.limsup_eq
  have h₂ := ht.liminf_eq
  rw [hsup] at h₁
  rw [hinf] at h₂
  linarith

def additiveAlternation (n : ℕ) : ℝ := (-1)^n+1/((n : ℝ)+1)

theorem additive_alternation_subsequences :
    Tendsto (fun n => additiveAlternation (2*n)) atTop (𝓝 1) ∧
    Tendsto (fun n => additiveAlternation (2*n+1)) atTop (𝓝 (-1)) := by
  constructor
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).add (reciprocal_tail.comp even_indices_atTop)
    simpa [additiveAlternation,Function.comp_def,pow_mul] using h
  · have h := (tendsto_const_nhds (x := (-1 : ℝ))).add (reciprocal_tail.comp odd_indices_atTop)
    simpa [additiveAlternation,Function.comp_def,pow_succ,pow_mul] using h

theorem additive_alternation_bounds (n : ℕ) :
    -1 < additiveAlternation n ∧ additiveAlternation n ≤ 2 := by
  have hp : 0 < 1/((n : ℝ)+1) := by positivity
  have hsmall : 1/((n : ℝ)+1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; have hn := Nat.cast_nonneg (α := ℝ) n; linarith
  have hpow : |(-1 : ℝ)^n|=1 := by simp
  have hsign := abs_le.mp (le_of_eq hpow)
  dsimp [additiveAlternation]
  constructor <;> linarith

theorem additive_alternation_extrema :
    IsLUB (range additiveAlternation) 2 ∧ IsGLB (range additiveAlternation) (-1) ∧
      (2 : ℝ) ∈ range additiveAlternation ∧ (-1 : ℝ) ∉ range additiveAlternation := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨0,by norm_num [additiveAlternation]⟩,?_⟩
  · rintro x ⟨n,rfl⟩; exact (additive_alternation_bounds n).2
  · intro x hx; have h := hx (mem_range_self 0); norm_num [additiveAlternation] at h; exact h
  · rintro x ⟨n,rfl⟩; exact (additive_alternation_bounds n).1.le
  · intro x hx
    have h := ge_of_tendsto (additive_alternation_subsequences.2)
      (Eventually.of_forall fun n => hx (mem_range_self (2*n+1)))
    exact h
  · rintro ⟨n,hn⟩; have h := (additive_alternation_bounds n).1; linarith

theorem additive_alternation_lims :
    limsup additiveAlternation atTop=1 ∧ liminf additiveAlternation atTop= -1 ∧
      ¬ ∃ l : ℝ, Tendsto additiveAlternation atTop (𝓝 l) := by
  apply alternating_limits additiveAlternation (fun n => 1/((n : ℝ)+1))
  · intro n; have h := additive_alternation_bounds n; constructor <;> linarith [h.1,h.2]
  · intro n
    have hpow : |(-1 : ℝ)^n|=1 := by simp
    have hs := abs_le.mp (le_of_eq hpow)
    have hp : 0 ≤ 1/((n : ℝ)+1) := by positivity
    dsimp [additiveAlternation]; constructor <;> linarith [hs.1,hs.2]
  · exact reciprocal_tail
  · exact additive_alternation_subsequences.1
  · exact additive_alternation_subsequences.2

def multiplicativeAlternation (n : ℕ) : ℝ := (-1)^n*(1+1/((n : ℝ)+1))

theorem multiplicative_alternation_subsequences :
    Tendsto (fun n => multiplicativeAlternation (2*n)) atTop (𝓝 1) ∧
    Tendsto (fun n => multiplicativeAlternation (2*n+1)) atTop (𝓝 (-1)) := by
  constructor
  · have h := (tendsto_const_nhds (x := (1 : ℝ))).add (reciprocal_tail.comp even_indices_atTop)
    simpa [multiplicativeAlternation,Function.comp_def,pow_mul] using h
  · have h := ((tendsto_const_nhds (x := (1 : ℝ))).add (reciprocal_tail.comp odd_indices_atTop)).neg
    simpa [multiplicativeAlternation,Function.comp_def,pow_succ,pow_mul] using h

theorem multiplicative_alternation_bounds (n : ℕ) :
    -(3/2 : ℝ) ≤ multiplicativeAlternation n ∧ multiplicativeAlternation n ≤ 2 := by
  have hp : 0 ≤ 1/((n : ℝ)+1) := by positivity
  have hsmall : 1/((n : ℝ)+1) ≤ 1 := by
    rw [div_le_iff₀ (by positivity)]; have hn := Nat.cast_nonneg (α := ℝ) n; linarith
  rcases Nat.even_or_odd n with he | ho
  · rcases he with ⟨k,hk⟩
    have heq : n=2*k := by omega
    rw [heq] at hp hsmall ⊢
    simp only [multiplicativeAlternation,pow_mul,neg_one_sq,one_pow,one_mul]
    constructor <;> linarith
  · rcases ho with ⟨k,hk⟩
    subst n
    have hhalf : 1/(((2*k+1 : ℕ) : ℝ)+1) ≤ 1/2 := by
      rw [div_le_iff₀ (by positivity)]
      push_cast
      have hn := Nat.cast_nonneg (α := ℝ) k
      linarith
    simp only [multiplicativeAlternation,pow_succ,pow_mul,neg_one_sq,one_pow,
      one_mul,mul_neg_one]
    constructor <;> linarith

theorem multiplicative_alternation_extrema :
    IsLUB (range multiplicativeAlternation) 2 ∧
      IsGLB (range multiplicativeAlternation) (-(3/2)) ∧
      (2 : ℝ) ∈ range multiplicativeAlternation ∧
      (-(3/2) : ℝ) ∈ range multiplicativeAlternation := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨0,by norm_num [multiplicativeAlternation]⟩,
    ⟨1,by norm_num [multiplicativeAlternation]⟩⟩
  · rintro x ⟨n,rfl⟩; exact (multiplicative_alternation_bounds n).2
  · intro x hx; have h := hx (mem_range_self 0); norm_num [multiplicativeAlternation] at h; exact h
  · rintro x ⟨n,rfl⟩; exact (multiplicative_alternation_bounds n).1
  · intro x hx; have h := hx (mem_range_self 1); norm_num [multiplicativeAlternation] at h; linarith

theorem multiplicative_alternation_lims :
    limsup multiplicativeAlternation atTop=1 ∧ liminf multiplicativeAlternation atTop= -1 ∧
      ¬ ∃ l : ℝ, Tendsto multiplicativeAlternation atTop (𝓝 l) := by
  apply alternating_limits multiplicativeAlternation (fun n => 1/((n : ℝ)+1))
  · intro n; have h := multiplicative_alternation_bounds n; constructor <;> linarith [h.1,h.2]
  · intro n
    have hpow : |(-1 : ℝ)^n|=1 := by simp
    have hs := abs_le.mp (le_of_eq hpow)
    have hp : 0 ≤ 1/((n : ℝ)+1) := by positivity
    have hh := mul_le_mul_of_nonneg_right hs.1 (by linarith : 0 ≤ 1+1/((n : ℝ)+1))
    have hh' := mul_le_mul_of_nonneg_right hs.2 (by linarith : 0 ≤ 1+1/((n : ℝ)+1))
    dsimp [multiplicativeAlternation]; constructor <;> linarith
  · exact reciprocal_tail
  · exact multiplicative_alternation_subsequences.1
  · exact multiplicative_alternation_subsequences.2

theorem tolerance_all_future (T : ℕ) :
    (∀ t ≥ T, |(3 : ℝ)/((t : ℝ)+1)| < 1/10) ↔ 30 ≤ T := by
  have h (t : ℕ) : |(3 : ℝ)/((t : ℝ)+1)|=(3 : ℝ)/((t : ℝ)+1) :=
    abs_of_nonneg (by positivity)
  simp only [h]
  constructor
  · intro h; exact SafeLearning.PrimersFoundations.sequence_threshold T |>.mp (h T le_rfl)
  · intro h t ht; exact SafeLearning.PrimersFoundations.sequence_threshold t |>.mpr (h.trans ht)

end SafeLearning.CompleteFoundationsSequences
