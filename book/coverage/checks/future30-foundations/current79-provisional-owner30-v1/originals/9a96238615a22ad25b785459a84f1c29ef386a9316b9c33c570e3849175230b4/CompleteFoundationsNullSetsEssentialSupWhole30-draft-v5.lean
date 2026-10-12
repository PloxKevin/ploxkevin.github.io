import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.Data.EReal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
open Set Filter MeasureTheory Metric
open scoped ENNReal NNReal BigOperators Topology

namespace SafeLearning.CompleteFoundationsNullSetsEssentialSupWhole30

-- None pads a finite or empty box family with empty sets; Some is an actual closed coordinate box.
abbrev SourceBox (I : Type*) := Option ((I → ℝ) × (I → ℝ))
def boxSet {I : Type*} (B : SourceBox I) : Set (I → ℝ) :=
  match B with
  | none => ∅
  | some (a,b) => Set.pi univ (fun i => Icc (a i) (b i))
def boxContent {I : Type*} [Fintype I] (B : SourceBox I) : ℝ≥0∞ :=
  match B with
  | none => 0
  | some (a,b) => ∏ i, ENNReal.ofReal (b i-a i)
def sourceNull {I : Type*} [Fintype I] (N : Set (I → ℝ)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B : ℕ → SourceBox I,
    N ⊆ ⋃ j, boxSet (B j) ∧ (∑' j, boxContent (B j)) < ENNReal.ofReal ε

theorem actual_coordinate_box_content_is_its_lebesgue_volume
    {I : Type*} [Fintype I] (B : SourceBox I) : volume (boxSet B) = boxContent B := by
  cases B with
  | none => simp [boxSet,boxContent]
  | some p => simpa only [boxSet,boxContent,pi_univ_Icc] using (@Real.volume_Icc_pi I _ p.1 p.2)

theorem actual_bounded_diameter_set_has_a_genuine_enclosing_box
    {I : Type*} [Fintype I] (s : Set (I → ℝ)) (hs : ediam s ≠ ∞) :
    ∃ B : SourceBox I, s ⊆ boxSet B ∧
      boxContent B ≤ (2 : ℝ≥0∞)^Fintype.card I *
        (⨆ _ : s.Nonempty,ediam s ^ Fintype.card I) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨x,hx⟩
  · exact ⟨none,by simp [boxSet],by simp [boxContent]⟩
  let r : ℝ := diam s
  refine ⟨some (fun i => x i-r, fun i => x i+r),?_,?_⟩
  · intro y hy
    change ∀ i ∈ univ, x i-r ≤ y i ∧ y i ≤ x i+r
    intro i _
    have hi := (LipschitzWith.eval i).dist_le_mul y x
    have hd := Metric.dist_le_diam_of_mem' hs hy hx
    have hi' : dist (y i) (x i) ≤ dist y x := by
      simpa only [NNReal.coe_one,one_mul] using hi
    have ha : |y i-x i| ≤ r := by
      simpa only [Real.dist_eq] using hi'.trans hd
    exact ⟨by linarith [(abs_le.mp ha).1],by linarith [(abs_le.mp ha).2]⟩
  · simp only [iSup_pos (show s.Nonempty from ⟨x,hx⟩)]
    change (∏ i : I, ENNReal.ofReal ((x i+r)-(x i-r))) ≤ _
    simp only [show ∀ i, (x i+r)-(x i-r)=2*r by intro i;ring]
    rw [Finset.prod_const,Finset.card_univ,ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat, mul_pow]
    exact le_of_eq (by dsimp only [r,Metric.diam];rw [ENNReal.ofReal_toReal hs])

theorem actual_lebesgue_null_set_has_countable_boxes_of_arbitrarily_small_total_volume
    {I : Type*} [Fintype I] (N : Set (I → ℝ)) (hN : volume N = 0) : sourceNull N := by
  classical
  intro ε hε
  let C : ℝ≥0∞ := (2 : ℝ≥0∞)^Fintype.card I
  have hC0 : C ≠ 0 := pow_ne_zero _ (by norm_num)
  have hCt : C ≠ ∞ := ENNReal.pow_ne_top (by norm_num)
  have hδ : 0 < ENNReal.ofReal ε / C := by
    exact ENNReal.div_pos_iff.mpr ⟨by exact (ENNReal.ofReal_pos.mpr hε).ne',hCt⟩
  have hh : (Measure.hausdorffMeasure (Fintype.card I : ℝ) : Measure (I → ℝ)) N = 0 := by
    simpa only [hausdorffMeasure_pi_real] using hN
  rw [Measure.hausdorffMeasure_apply] at hh
  have hc : (⨅ (t : ℕ → Set (I → ℝ)) (_ : N ⊆ ⋃ j,t j) (_ : ∀ j,ediam (t j) ≤ (1 : ℝ≥0∞)),
      ∑' j, ⨆ _ : (t j).Nonempty, ediam (t j) ^ (Fintype.card I : ℝ)) < ENNReal.ofReal ε / C := by
    have hu := iSup_le_iff.mp hh.le 1
    have hu' := iSup_le_iff.mp hu (by norm_num : (0 : ℝ≥0∞) < 1)
    exact hu'.trans_lt hδ
  rcases iInf_lt_iff.mp hc with ⟨t,ht⟩
  rcases iInf_lt_iff.mp ht with ⟨hcover,ht⟩
  rcases iInf_lt_iff.mp ht with ⟨hdiam,ht⟩
  choose B hB hcost using fun j =>
    actual_bounded_diameter_set_has_a_genuine_enclosing_box (t j)
      (ne_of_lt ((hdiam j).trans_lt (by norm_num : (1 : ℝ≥0∞) < ∞)))
  refine ⟨B,hcover.trans (iUnion_mono hB),?_⟩
  have hm : (∑' j,boxContent (B j)) ≤
      C * (∑' j, ⨆ _ : (t j).Nonempty, ediam (t j) ^ (Fintype.card I : ℝ)) := by
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro j
    simpa only [ENNReal.rpow_natCast] using hcost j
  have hmul := ENNReal.mul_lt_mul_left hC0 hCt ht
  exact hm.trans_lt (by simpa only [ENNReal.div_mul_cancel hC0 hCt,mul_comm] using hmul)

theorem actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume
    {I : Type*} [Fintype I] (N : Set (I → ℝ)) : sourceNull N ↔ volume N=0 := by
  constructor
  · intro h
    apply le_antisymm ?_ zero_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    rcases h ε (NNReal.coe_pos.mpr hε) with ⟨B,hB,hcost⟩
    have hh : volume N ≤ ENNReal.ofReal (ε : ℝ) := (measure_mono hB).trans ((measure_iUnion_le fun j => boxSet (B j)).trans
      (by simpa only [actual_coordinate_box_content_is_its_lebesgue_volume] using hcost.le))
    simpa only [zero_add,ENNReal.ofReal_coe_nnreal] using hh
  · exact actual_lebesgue_null_set_has_countable_boxes_of_arbitrarily_small_total_volume N

theorem actual_finite_sets_are_null_in_positive_coordinate_dimension
    {I : Type*} [Fintype I] [Nonempty I] (N : Set (I → ℝ)) (hN : N.Finite) : sourceNull N :=
  (actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume N).2 (hN.measure_zero volume)

theorem actual_strict_affine_subspaces_have_countable_null_box_covers
    {I : Type*} [Fintype I] (A : AffineSubspace ℝ (I → ℝ)) (hA : A ≠ ⊤) :
    sourceNull (A : Set (I → ℝ)) :=
  (actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume _).2
    (Measure.addHaar_affineSubspace volume A hA)

theorem actual_nonzero_linear_normal_defines_a_null_affine_hyperplane
    {I : Type*} [Fintype I] (L : (I → ℝ) →ₗ[ℝ] ℝ) (hL : L ≠ 0) (b : ℝ) :
    sourceNull {x | L x+b=0} := by
  let A : AffineSubspace ℝ (I → ℝ) := ({-b} : AffineSubspace ℝ ℝ).comap L.toAffineMap
  have hA : A ≠ ⊤ := by
    intro h
    have he (x : I → ℝ) : L x = -b := by
      have hx : x ∈ A := h ▸ AffineSubspace.mem_top ℝ (I→ℝ) x
      simpa [A,AffineSubspace.mem_comap] using hx
    have hb := he 0
    apply hL
    ext x
    change L x=0
    simpa only [map_zero] using (he x).trans hb.symm
  have hh := actual_strict_affine_subspaces_have_countable_null_box_covers A hA
  convert hh using 1
  ext x
  simp only [A,AffineSubspace.coe_comap,LinearMap.coe_toAffineMap,mem_preimage,
    AffineSubspace.coe_singleton,mem_singleton_iff,mem_ofPred_eq]
  exact add_eq_zero_iff_eq_neg

def normalMap {I : Type*} [Fintype I] (w : I → ℝ) : (I → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i,w i*x i
  map_add' x y := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _;ring

theorem actual_nonzero_vector_normal_produces_a_nonzero_linear_functional
    {I : Type*} [Fintype I] (w : I → ℝ) (hw : w ≠ 0) : normalMap w ≠ 0 := by
  classical
  intro h
  apply hw
  funext j
  have hj : normalMap w (Pi.single j 1)=0 := by rw [h];rfl
  simpa [normalMap,Pi.single_apply] using hj

theorem actual_printed_dot_product_hyperplanes_with_nonzero_normal_are_null
    {I : Type*} [Fintype I] (w : I → ℝ) (hw : w ≠ 0) (b : ℝ) :
    sourceNull {x | (∑ i,w i*x i)+b=0} := by
  exact actual_nonzero_linear_normal_defines_a_null_affine_hyperplane (normalMap w)
    (actual_nonzero_vector_normal_produces_a_nonzero_linear_functional w hw) b

theorem actual_subsets_of_a_null_set_are_null
    {I : Type*} [Fintype I] {N M : Set (I → ℝ)} (hNM : N ⊆ M) (hM : sourceNull M) : sourceNull N := by
  intro ε hε
  rcases hM ε hε with ⟨B,hB,hc⟩
  exact ⟨B,hNM.trans hB,hc⟩

theorem actual_all_affine_lines_in_the_plane_are_null
    (p v : Fin 2 → ℝ) : sourceNull (Set.range (fun t : ℝ => p+t • v)) := by
  classical
  by_cases hv : v=0
  · subst v
    apply actual_subsets_of_a_null_set_are_null (M:=({p} : Set (Fin 2→ℝ)))
    · simp
    · exact actual_finite_sets_are_null_in_positive_coordinate_dimension _ (finite_singleton p)
  let w : Fin 2 → ℝ := ![-v 1,v 0]
  have hw : w ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    apply hv
    funext i
    fin_cases i <;> simp [w] at h0 h1 ⊢ <;> linarith
  have hh := actual_printed_dot_product_hyperplanes_with_nonzero_normal_are_null w hw
    (-(∑ i,w i*p i))
  apply actual_subsets_of_a_null_set_are_null (hM:=hh)
  rintro x ⟨t,rfl⟩
  change (∑ i,w i*(p+t • v) i)-(∑ i,w i*p i)=0
  simp only [Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  dsimp [w]
  ring

theorem actual_finite_unions_of_null_sets_are_null
    {I J : Type*} [Fintype I] (F : Finset J) (N : J → Set (I → ℝ))
    (hN : ∀ j ∈ F,sourceNull (N j)) : sourceNull (⋃ j∈F,N j) := by
  apply (actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume _).2
  exact (measure_biUnion_null_iff F.finite_toSet.countable).mpr (fun j hj =>
    (actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume _).1 (hN j hj))

theorem actual_ae_means_failure_on_a_null_set
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (P : Ω → Prop) :
    (∀ᵐ ω ∂μ,P ω) ↔ μ {ω | ¬P ω}=0 := Iff.rfl

theorem actual_euclidean_ae_is_exactly_a_countably_box_coverable_failure_set
    {I : Type*} [Fintype I] (P : (I → ℝ) → Prop) :
    (∀ᵐ x ∂volume,P x) ↔ sourceNull {x | ¬P x} := by
  rw [actual_ae_means_failure_on_a_null_set,
    actual_countable_arbitrarily_small_box_cover_is_exactly_null_volume]

theorem actual_as_means_probability_one_for_a_measurable_event
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Set Ω) (hA : MeasurableSet A) : (∀ᵐ ω ∂μ,ω∈A) ↔ μ A=1 :=
  mem_ae_iff_prob_eq_one hA

-- Extended-real bounds also handle an unbounded real random variable honestly.
def sourceEssentialSup {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Z : Ω → EReal) : EReal :=
  sInf {c | μ {ω | Z ω ≤ c}=1}

theorem actual_essential_supremum_infimum_formula_is_the_extended_essSup
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → EReal) (hZ : Measurable Z) : sourceEssentialSup μ Z=essSup Z μ := by
  unfold sourceEssentialSup
  rw [essSup_eq_sInf]
  congr 1
  ext c
  change μ {ω | Z ω ≤ c}=1 ↔ μ {x | c < Z x}=0
  rw [← mem_ae_iff_prob_eq_one (measurableSet_le hZ measurable_const)]
  simp only [mem_ae_iff,compl_ofPred,not_le]

theorem actual_extended_essential_supremum_is_the_smallest_almost_sure_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → EReal) (hZ : Measurable Z) :
    IsLeast {c : EReal | μ {ω | Z ω ≤ c}=1} (sourceEssentialSup μ Z) := by
  rw [actual_essential_supremum_infimum_formula_is_the_extended_essSup μ Z hZ]
  refine ⟨?_,?_⟩
  · exact (mem_ae_iff_prob_eq_one (measurableSet_le hZ measurable_const)).1 ae_le_essSup
  · intro c hc
    exact essSup_le_of_ae_le c ((mem_ae_iff_prob_eq_one (measurableSet_le hZ measurable_const)).2 hc)

theorem actual_real_random_variable_has_an_extended_smallest_almost_sure_upper_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ : Measurable Z) :
    IsLeast {c : EReal | μ {ω | (Z ω : EReal) ≤ c}=1}
      (sourceEssentialSup μ (fun ω => (Z ω : EReal))) := by
  exact actual_extended_essential_supremum_is_the_smallest_almost_sure_upper_bound μ _
    (continuous_coe_real_ereal.measurable.comp hZ)

end SafeLearning.CompleteFoundationsNullSetsEssentialSupWhole30
