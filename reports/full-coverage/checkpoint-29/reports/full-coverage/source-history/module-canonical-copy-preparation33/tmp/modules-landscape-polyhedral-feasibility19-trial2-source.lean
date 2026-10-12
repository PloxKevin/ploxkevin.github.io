import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal BigOperators

namespace SafeLearning.CompleteModulesLandscapePolyhedralFeasibility

/-- Finite lower and upper bounds have a common real point exactly when every
lower bound is at most every upper bound. Empty sides are allowed. -/
theorem actual_finite_bounds_have_a_common_real_point
    (L R : Set ℝ) (hL : L.Finite) (hR : R.Finite)
    (hcross : ∀ l ∈ L, ∀ r ∈ R, l ≤ r) :
    ∃ x : ℝ, (∀ l ∈ L, l ≤ x) ∧ ∀ r ∈ R, x ≤ r := by
  by_cases hneL : L.Nonempty
  · refine ⟨sSup L,fun l hl => le_csSup hL.bddAbove hl,?_⟩
    intro r hr
    exact csSup_le hneL (fun l hl => hcross l hl r hr)
  · by_cases hneR : R.Nonempty
    · refine ⟨sInf R,?_,fun r hr => csInf_le hR.bddBelow hr⟩
      intro l hl
      exact (hneL ⟨l,hl⟩).elim
    · exact ⟨0,fun l hl => (hneL ⟨l,hl⟩).elim,fun r hr => (hneR ⟨r,hr⟩).elim⟩

/-- A real Fourier–Motzkin elimination step for an arbitrary finite family. -/
theorem actual_finite_scalar_linear_elimination
    {I : Type*} [Fintype I] (a d : I → ℝ) :
    (∃ x : ℝ, ∀ i, a i * x + d i ≤ 0) ↔
      (∀ i, a i = 0 → d i ≤ 0) ∧
      (∀ i j, a i < 0 → 0 < a j → d i / (-a i) + d j / a j ≤ 0) := by
  classical
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun i hi => by simpa only [hi,zero_mul,zero_add] using hx i,?_⟩
    intro i j hi hj
    have hl : d i / (-a i) ≤ x := (div_le_iff₀ (neg_pos.mpr hi)).mpr (by nlinarith [hx i])
    have hu : x ≤ -d j / a j := (le_div_iff₀ hj).mpr (by nlinarith [hx j])
    rw [neg_div] at hu
    linarith
  · rintro ⟨hzero,hpair⟩
    let L : Set ℝ := (fun i => d i / (-a i)) '' {i | a i < 0}
    let R : Set ℝ := (fun j => -d j / a j) '' {j | 0 < a j}
    have hcross : ∀ l ∈ L, ∀ r ∈ R, l ≤ r := by
      rintro l ⟨i,hi,rfl⟩ r ⟨j,hj,rfl⟩
      have hp := hpair i j hi hj
      change d i / (-a i) ≤ -d j / a j
      rw [neg_div]
      linarith
    obtain ⟨x,hl,hu⟩ := actual_finite_bounds_have_a_common_real_point L R
      (Set.toFinite L) (Set.toFinite R) hcross
    refine ⟨x,?_⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hb := hl (d i / (-a i)) (mem_image_of_mem _ hi)
      have hb' := (div_le_iff₀ (neg_pos.mpr hi)).mp hb
      nlinarith
    · simpa only [hi,zero_mul,zero_add] using hzero i hi
    · have hb := hu (-d i / a i) (mem_image_of_mem _ hi)
      have hb' := (le_div_iff₀ hi).mp hb
      nlinarith

/-- Eliminating finitely many real coordinates from finitely many non-strict
linear inequalities produces a closed parameter set. The parameter terms may
be any continuous real functions. No image-closedness premise is assumed. -/
theorem actual_finite_linear_system_projection_is_closed
    (m : ℕ) {I X : Type*} [Fintype I] [TopologicalSpace X]
    (A : I → Fin m → ℝ) (g : I → X → ℝ) (hg : ∀ i, Continuous (g i)) :
    IsClosed {z : X | ∃ x : Fin m → ℝ, ∀ i, (∑ j, A i j * x j) + g i z ≤ 0} := by
  classical
  induction m generalizing I with
  | zero =>
    have he : {z : X | ∃ x : Fin 0 → ℝ, ∀ i, (∑ j, A i j * x j) + g i z ≤ 0} =
        ⋂ i, {z : X | g i z ≤ 0} := by
      ext z
      simp only [mem_ofPred_eq,mem_iInter]
      constructor
      · rintro ⟨x,hx⟩ i
        simpa using hx i
      · intro hz
        exact ⟨fun _ => 0,fun i => by simpa using hz i⟩
    rw [he]
    exact isClosed_iInter (fun i => isClosed_le (hg i) continuous_const)
  | succ m ih =>
    let a : I → ℝ := fun i => A i 0
    let A' : (I ⊕ (I × I)) → Fin m → ℝ := fun k j => match k with
      | .inl i => if a i = 0 then A i j.succ else 0
      | .inr (i,l) => if a i < 0 ∧ 0 < a l then A i j.succ / (-a i) + A l j.succ / a l else 0
    let g' : (I ⊕ (I × I)) → X → ℝ := fun k z => match k with
      | .inl i => if a i = 0 then g i z else 0
      | .inr (i,l) => if a i < 0 ∧ 0 < a l then g i z / (-a i) + g l z / a l else 0
    have hg' : ∀ k, Continuous (g' k) := by
      intro k
      rcases k with i | ⟨i,l⟩
      · by_cases h : a i = 0
        · simpa only [g',ite_eq_left h] using hg i
        · simpa only [g',ite_eq_right h] using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))
      · by_cases h : a i < 0 ∧ 0 < a l
        · simpa only [g',ite_eq_left h,Pi.add_apply] using (hg i).div_const (-a i) |>.add ((hg l).div_const (a l))
        · simpa only [g',ite_eq_right h] using (continuous_const : Continuous (fun _ : X => (0 : ℝ)))
    have hsingle (i : I) (v : Fin m → ℝ) (z : X) (hi : a i = 0) :
        (∑ j, A' (.inl i) j * v j) + g' (.inl i) z =
          (∑ j, A i j.succ * v j) + g i z := by
      simp only [A',g',ite_eq_left hi]
    have hpair (i l : I) (v : Fin m → ℝ) (z : X) (h : a i < 0 ∧ 0 < a l) :
        (∑ j, A' (.inr (i,l)) j * v j) + g' (.inr (i,l)) z =
          ((∑ j, A i j.succ * v j) + g i z) / (-a i) +
          ((∑ j, A l j.succ * v j) + g l z) / a l := by
      simp only [A',g',ite_eq_left h,add_mul,div_mul_eq_mul_div,Finset.sum_add_distrib]
      rw [← Finset.sum_div,← Finset.sum_div]
      ring
    have he : {z : X | ∃ x : Fin (m + 1) → ℝ, ∀ i, (∑ j, A i j * x j) + g i z ≤ 0} =
        {z : X | ∃ v : Fin m → ℝ, ∀ k, (∑ j, A' k j * v j) + g' k z ≤ 0} := by
      ext z
      change (∃ x : Fin (m + 1) → ℝ, ∀ i, (∑ j, A i j * x j) + g i z ≤ 0) ↔ _
      constructor
      · rintro ⟨x,hx⟩
        let v : Fin m → ℝ := fun j => x j.succ
        have hs : ∃ r : ℝ, ∀ i, a i * r + ((∑ j, A i j.succ * v j) + g i z) ≤ 0 := by
          refine ⟨x 0,?_⟩
          intro i
          simpa only [a,v,Fin.sum_univ_succ,add_assoc] using hx i
        have hc := (actual_finite_scalar_linear_elimination a
          (fun i => (∑ j, A i j.succ * v j) + g i z)).mp hs
        refine ⟨v,?_⟩
        intro k
        rcases k with i | ⟨i,l⟩
        · by_cases hi : a i = 0
          · rw [hsingle i v z hi]
            exact hc.1 i hi
          · simp only [A',g',ite_eq_right hi,zero_mul,Finset.sum_const_zero,zero_add,le_refl]
        · by_cases h : a i < 0 ∧ 0 < a l
          · rw [hpair i l v z h]
            exact hc.2 i l h.1 h.2
          · simp only [A',g',ite_eq_right h,zero_mul,Finset.sum_const_zero,zero_add,le_refl]
      · rintro ⟨v,hv⟩
        have hc : (∀ i, a i = 0 → (∑ j, A i j.succ * v j) + g i z ≤ 0) ∧
            (∀ i l, a i < 0 → 0 < a l →
              ((∑ j, A i j.succ * v j) + g i z) / (-a i) +
              ((∑ j, A l j.succ * v j) + g l z) / a l ≤ 0) := by
          constructor
          · intro i hi
            rw [← hsingle i v z hi]
            exact hv (.inl i)
          · intro i l hi hl
            rw [← hpair i l v z ⟨hi,hl⟩]
            exact hv (.inr (i,l))
        obtain ⟨r,hr⟩ := (actual_finite_scalar_linear_elimination a
          (fun i => (∑ j, A i j.succ * v j) + g i z)).mpr hc
        refine ⟨Fin.cons r v,?_⟩
        intro i
        simpa only [a,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,add_assoc] using hr i
    rw [he]
    exact ih A' g' hg'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine objective image of a finite H-polyhedron is actually closed.
The proof eliminates all input coordinates, including two inequalities for
the objective equality; no Minkowski–Weyl or attainment premise is used. -/
theorem actual_affine_objective_image_of_a_finite_closed_polyhedron_is_closed
    (n : ℕ) (A : Fin n → E →ₗ[ℝ] ℝ) (b : Fin n → ℝ)
    (c : E →ₗ[ℝ] ℝ) (a : ℝ) :
    IsClosed ((fun u : E => c u + a) '' {u | ∀ i, A i u ≤ b i}) := by
  classical
  let m : ℕ := Module.finrank ℝ E
  let basis := Module.finBasis ℝ E
  let e := basis.equivFun
  have hsum (L : E →ₗ[ℝ] ℝ) (x : Fin m → ℝ) :
      (∑ j, L (basis j) * x j) = L (e.symm x) := by
    rw [Module.Basis.equivFun_symm_apply, map_sum]
    simp only [map_smul,smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  let A' : (Fin n ⊕ (Unit ⊕ Unit)) → Fin m → ℝ := fun k j => match k with
    | .inl i => A i (basis j)
    | .inr (.inl _) => c (basis j)
    | .inr (.inr _) => -c (basis j)
  let g' : (Fin n ⊕ (Unit ⊕ Unit)) → ℝ → ℝ := fun k r => match k with
    | .inl i => -b i
    | .inr (.inl _) => a - r
    | .inr (.inr _) => -a + r
  have hg' : ∀ k, Continuous (g' k) := by
    intro k
    rcases k with i | (u | u)
    · exact continuous_const
    · exact continuous_const.sub continuous_id
    · exact continuous_const.add continuous_id
  have he : ((fun u : E => c u + a) '' {u | ∀ i, A i u ≤ b i}) =
      {r : ℝ | ∃ x : Fin m → ℝ, ∀ k, (∑ j, A' k j * x j) + g' k r ≤ 0} := by
    ext r
    constructor
    · rintro ⟨u,hu,hvalue⟩
      refine ⟨e u,?_⟩
      intro k
      rcases k with i | (z | z)
      · change (∑ j, A i (basis j) * (e u) j) + -b i ≤ 0
        rw [hsum,e.symm_apply_apply]
        linarith [hu i]
      · change (∑ j, c (basis j) * (e u) j) + (a - r) ≤ 0
        rw [hsum,e.symm_apply_apply]
        linarith
      · change (∑ j, -c (basis j) * (e u) j) + (-a + r) ≤ 0
        simp only [neg_mul,Finset.sum_neg_distrib]
        rw [hsum,e.symm_apply_apply]
        linarith
    · rintro ⟨x,hx⟩
      refine ⟨e.symm x,?_,?_⟩
      · intro i
        have hi := hx (.inl i)
        change (∑ j, A i (basis j) * x j) + -b i ≤ 0 at hi
        rw [hsum] at hi
        linarith
      · have h1 := hx (.inr (.inl ()))
        have h2 := hx (.inr (.inr ()))
        change (∑ j, c (basis j) * x j) + (a - r) ≤ 0 at h1
        change (∑ j, -c (basis j) * x j) + (-a + r) ≤ 0 at h2
        simp only [neg_mul,Finset.sum_neg_distrib] at h2
        rw [hsum] at h1 h2
        linarith
  rw [he]
  exact actual_finite_linear_system_projection_is_closed m A' g' hg'

/-- The true extended-real supremum of an affine objective over an arbitrary
finite closed H-polyhedron yields a feasible nonnegative input. The input set
need not be bounded; nonemptiness and the necessary endpoint membership are
derived rather than assumed. -/
theorem actual_nonnegative_extended_supremum_on_a_closed_polyhedron_yields_feasible_input
    (n : ℕ) (A : Fin n → E →ₗ[ℝ] ℝ) (b : Fin n → ℝ)
    (c : E →ₗ[ℝ] ℝ) (a : ℝ)
    (hsup : (0 : EReal) ≤ sSup ((fun u : E => ((c u + a : ℝ) : EReal)) ''
      {u | ∀ i, A i u ≤ b i})) :
    ∃ u : E, (∀ i, A i u ≤ b i) ∧ 0 ≤ c u + a := by
  classical
  let U : Set E := {u | ∀ i, A i u ≤ b i}
  let S : Set ℝ := (fun u : E => c u + a) '' U
  have hU : U.Nonempty := by
    by_contra hempty
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    change (0 : EReal) ≤ sSup ((fun u : E => ((c u + a : ℝ) : EReal)) '' U) at hsup
    simp only [he,Set.image_empty,sSup_empty] at hsup
    exact (not_le_of_gt EReal.bot_lt_zero) hsup
  have hS : S.Nonempty := hU.image (fun u => c u + a)
  have hclosed : IsClosed S :=
    actual_affine_objective_image_of_a_finite_closed_polyhedron_is_closed n A b c a
  by_cases hbound : BddAbove S
  · have hmem := hclosed.csSup_mem hS hbound
    have hupper : sSup ((fun u : E => ((c u + a : ℝ) : EReal)) '' U) ≤
        ((sSup S : ℝ) : EReal) := by
      apply sSup_le
      rintro v ⟨u,hu,rfl⟩
      exact EReal.coe_le_coe_iff.mpr (le_csSup hbound (mem_image_of_mem (fun u => c u + a) hu))
    have hnonneg : 0 ≤ sSup S := EReal.coe_nonneg.mp (hsup.trans hupper)
    obtain ⟨u,hu,hvalue⟩ := hmem
    exact ⟨u,hu,by simpa only [hvalue] using hnonneg⟩
  · by_contra hno
    push Not at hno
    apply hbound
    refine ⟨0,?_⟩
    rintro r ⟨u,hu,rfl⟩
    exact (hno u hu).le

end SafeLearning.CompleteModulesLandscapePolyhedralFeasibility
