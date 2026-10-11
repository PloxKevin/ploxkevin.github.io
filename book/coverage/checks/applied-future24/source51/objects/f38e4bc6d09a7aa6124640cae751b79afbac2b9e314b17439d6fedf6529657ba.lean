import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteFoundationsPolygonLP

/-- A continuous linear objective reaches its maximum at an actual extreme point
    of every nonempty compact domain; convexity is not needed for this statement. -/
theorem actual_compact_linear_maximum_at_extreme_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set E) (hcompact : IsCompact domain) (hne : domain.Nonempty)
    (objective : E →L[ℝ] ℝ) :
    ∃ point ∈ domain.extremePoints ℝ, ∀ other ∈ domain, objective other ≤ objective point := by
  have hface : IsExposed ℝ domain
      {point ∈ domain | ∀ other ∈ domain, objective other ≤ objective point} :=
    fun _ => ⟨objective, rfl⟩
  obtain ⟨maximizer, hm, hmax⟩ :=
    hcompact.exists_isMaxOn hne objective.continuous.continuousOn
  obtain ⟨point, hp⟩ := (hface.isCompact hcompact).extremePoints_nonempty ⟨maximizer, hm, hmax⟩
  exact ⟨point, hface.isExtreme.extremePoints_subset_extremePoints hp, hp.1.2⟩

theorem actual_compact_linear_minimum_at_extreme_point
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (domain : Set E) (hcompact : IsCompact domain) (hne : domain.Nonempty)
    (objective : E →L[ℝ] ℝ) :
    ∃ point ∈ domain.extremePoints ℝ, ∀ other ∈ domain, objective point ≤ objective other := by
  obtain ⟨point, hp, hmax⟩ :=
    actual_compact_linear_maximum_at_extreme_point domain hcompact hne (-objective)
  refine ⟨point, hp, ?_⟩
  intro other ho
  have h := hmax other ho
  simpa only [neg_apply, neg_le_neg_iff] using h

def sourceFeasible (point : ℝ × ℝ) : Prop :=
  0 ≤ point.1 ∧ 0 ≤ point.2 ∧ point.1 + point.2 ≤ 3 ∧ point.1 ≤ 2

def sourcePolygon : Set (ℝ × ℝ) := {point | sourceFeasible point}
def sourceObjective (point : ℝ × ℝ) : ℝ := 2 * point.1 + point.2

theorem actual_polygon_nonempty : sourcePolygon.Nonempty :=
  ⟨(0,0), by norm_num [sourcePolygon, sourceFeasible]⟩

theorem actual_polygon_closed : IsClosed sourcePolygon := by
  have hf : Continuous (fun point : ℝ × ℝ => point.1) := continuous_fst
  have hs : Continuous (fun point : ℝ × ℝ => point.2) := continuous_snd
  exact (isClosed_le (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℝ))) hf).inter
    ((isClosed_le (continuous_const : Continuous (fun _ : ℝ × ℝ => (0:ℝ))) hs).inter
      ((isClosed_le (hf.add hs) (continuous_const : Continuous (fun _ : ℝ × ℝ => (3:ℝ)))).inter
        (isClosed_le hf (continuous_const : Continuous (fun _ : ℝ × ℝ => (2:ℝ))))))

theorem actual_polygon_in_closed_box : sourcePolygon ⊆ Icc ((0,0) : ℝ × ℝ) (2,3) := by
  intro point hp
  rcases hp with ⟨hx,hy,hxy,hx2⟩
  exact ⟨⟨hx,hy⟩,⟨hx2,by linarith⟩⟩

theorem actual_polygon_compact : IsCompact sourcePolygon :=
  isCompact_Icc.of_isClosed_subset actual_polygon_closed actual_polygon_in_closed_box

theorem actual_polygon_bounded : Bornology.IsBounded sourcePolygon :=
  actual_polygon_compact.isBounded

theorem actual_polygon_convex : Convex ℝ sourcePolygon := by
  intro first hf second hs left right hl hr hsum
  rcases hf with ⟨hfx,hfy,hfxy,hfx2⟩
  rcases hs with ⟨hsx,hsy,hsxy,hsx2⟩
  change 0 ≤ left * first.1 + right * second.1 ∧
    0 ≤ left * first.2 + right * second.2 ∧
    (left * first.1 + right * second.1) + (left * first.2 + right * second.2) ≤ 3 ∧
    left * first.1 + right * second.1 ≤ 2
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr hfxy),mul_nonneg hr (sub_nonneg.mpr hsxy)]
  · nlinarith [mul_nonneg hl (sub_nonneg.mpr hfx2),mul_nonneg hr (sub_nonneg.mpr hsx2)]

theorem actual_positive_weight_zero_sum (left right first second : ℝ)
    (hl : 0 < left) (hr : 0 < right) (hf : 0 ≤ first) (hs : 0 ≤ second)
    (hz : left * first + right * second = 0) : first = 0 ∧ second = 0 := by
  have hfprod : 0 ≤ left * first := mul_nonneg hl.le hf
  have hsprod : 0 ≤ right * second := mul_nonneg hr.le hs
  constructor <;> nlinarith

theorem actual_vertex_0_is_extreme :
    ((0,0) : ℝ × ℝ) ∈ sourcePolygon.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [sourcePolygon,sourceFeasible],?_⟩
  intro first hf second hs hsegment
  rcases hf with ⟨hfx,hfy,hfxy,hfx2⟩
  rcases hs with ⟨hsx,hsy,hsxy,hsx2⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left * first.1 + right * second.1 = 0 at hx
  change left * first.2 + right * second.2 = 0 at hy
  have ha : first.1 = 0 := (actual_positive_weight_zero_sum left right
    (first.1) (second.1) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  have hb : first.2 = 0 := (actual_positive_weight_zero_sum left right
    (first.2) (second.2) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext <;> change _ = _ <;> linarith

theorem actual_vertex_1_is_extreme :
    ((2,0) : ℝ × ℝ) ∈ sourcePolygon.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [sourcePolygon,sourceFeasible],?_⟩
  intro first hf second hs hsegment
  rcases hf with ⟨hfx,hfy,hfxy,hfx2⟩
  rcases hs with ⟨hsx,hsy,hsxy,hsx2⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left * first.1 + right * second.1 = 2 at hx
  change left * first.2 + right * second.2 = 0 at hy
  have ha : 2-first.1 = 0 := (actual_positive_weight_zero_sum left right
    (2-first.1) (2-second.1) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  have hb : first.2 = 0 := (actual_positive_weight_zero_sum left right
    (first.2) (second.2) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext <;> change _ = _ <;> linarith

theorem actual_vertex_2_is_extreme :
    ((2,1) : ℝ × ℝ) ∈ sourcePolygon.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [sourcePolygon,sourceFeasible],?_⟩
  intro first hf second hs hsegment
  rcases hf with ⟨hfx,hfy,hfxy,hfx2⟩
  rcases hs with ⟨hsx,hsy,hsxy,hsx2⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left * first.1 + right * second.1 = 2 at hx
  change left * first.2 + right * second.2 = 1 at hy
  have ha : 2-first.1 = 0 := (actual_positive_weight_zero_sum left right
    (2-first.1) (2-second.1) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  have hb : 3-first.1-first.2 = 0 := (actual_positive_weight_zero_sum left right
    (3-first.1-first.2) (3-second.1-second.2) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext <;> change _ = _ <;> linarith

theorem actual_vertex_3_is_extreme :
    ((0,3) : ℝ × ℝ) ∈ sourcePolygon.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [sourcePolygon,sourceFeasible],?_⟩
  intro first hf second hs hsegment
  rcases hf with ⟨hfx,hfy,hfxy,hfx2⟩
  rcases hs with ⟨hsx,hsy,hsxy,hsx2⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left * first.1 + right * second.1 = 0 at hx
  change left * first.2 + right * second.2 = 3 at hy
  have ha : first.1 = 0 := (actual_positive_weight_zero_sum left right
    (first.1) (second.1) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  have hb : 3-first.1-first.2 = 0 := (actual_positive_weight_zero_sum left right
    (3-first.1-first.2) (3-second.1-second.2) hl hr (by linarith) (by linarith)
    (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext <;> change _ = _ <;> linarith

theorem actual_three_positive_gaps_have_radius (first second third : ℝ)
    (hf : 0 < first) (hs : 0 < second) (ht : 0 < third) :
    ∃ radius : ℝ, 0 < radius ∧ radius < first ∧ radius < second ∧ radius < third := by
  refine ⟨min first (min second third)/2,?_,?_,?_,?_⟩
  · exact div_pos (lt_min hf (lt_min hs ht)) (by norm_num)
  · have h := min_le_left first (min second third); linarith
  · have h := (min_le_right first (min second third)).trans (min_le_left second third); linarith
  · have h := (min_le_right first (min second third)).trans (min_le_right second third); linarith

theorem actual_unlisted_point_has_two_sided_feasible_perturbation
    (point : ℝ × ℝ) (hp : point ∈ sourcePolygon)
    (h0 : point ≠ (0,0)) (h1 : point ≠ (2,0))
    (h2 : point ≠ (2,1)) (h3 : point ≠ (0,3)) :
    ∃ offset : ℝ × ℝ, offset ≠ 0 ∧ point-offset ∈ sourcePolygon ∧
      point+offset ∈ sourcePolygon := by
  rcases hp with ⟨hx,hy,hxy,hx2⟩
  by_cases hzero : point.1 = 0
  · have hyn : point.2 ≠ 0 := by intro h; exact h0 (Prod.ext hzero h)
    have hy3 : point.2 ≠ 3 := by intro h; exact h3 (Prod.ext hzero h)
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_three_positive_gaps_have_radius
      point.2 (3-point.2) 1 (by exact lt_of_le_of_ne hy (Ne.symm hyn))
      (by have h := lt_of_le_of_ne (by linarith : point.2 ≤ 3) hy3; linarith) (by norm_num)
    refine ⟨(0,radius),?_,?_,?_⟩
    · intro h; have hh := congrArg Prod.snd h; simpa using (ne_of_gt hr) hh
    · change sourceFeasible (point-(0,radius)); unfold sourceFeasible
      simp only [Prod.fst_sub,Prod.snd_sub]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change sourceFeasible (point+(0,radius)); unfold sourceFeasible
      simp only [Prod.fst_add,Prod.snd_add]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  by_cases hyzero : point.2 = 0
  · have hxne : point.1 ≠ 2 := by intro h; exact h1 (Prod.ext h hyzero)
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_three_positive_gaps_have_radius
      point.1 (2-point.1) 1 (lt_of_le_of_ne hx (Ne.symm hzero))
      (by have h := lt_of_le_of_ne hx2 hxne; linarith) (by norm_num)
    refine ⟨(radius,0),?_,?_,?_⟩
    · intro h; have hh := congrArg Prod.fst h; simpa using (ne_of_gt hr) hh
    · change sourceFeasible (point-(radius,0)); unfold sourceFeasible
      simp only [Prod.fst_sub,Prod.snd_sub]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change sourceFeasible (point+(radius,0)); unfold sourceFeasible
      simp only [Prod.fst_add,Prod.snd_add]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hxp : 0 < point.1 := lt_of_le_of_ne hx (Ne.symm hzero)
  have hyp : 0 < point.2 := lt_of_le_of_ne hy (Ne.symm hyzero)
  by_cases hxtwo : point.1 = 2
  · have hys : point.2 < 1 := by
      have hne : point.2 ≠ 1 := by intro h; exact h2 (Prod.ext hxtwo h)
      exact lt_of_le_of_ne (by linarith) hne
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_three_positive_gaps_have_radius
      point.2 (1-point.2) 1 hyp (by linarith) (by norm_num)
    refine ⟨(0,radius),?_,?_,?_⟩
    · intro h; have hh := congrArg Prod.snd h; simpa using (ne_of_gt hr) hh
    · change sourceFeasible (point-(0,radius)); unfold sourceFeasible
      simp only [Prod.fst_sub,Prod.snd_sub]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change sourceFeasible (point+(0,radius)); unfold sourceFeasible
      simp only [Prod.fst_add,Prod.snd_add]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hxs : point.1 < 2 := lt_of_le_of_ne hx2 hxtwo
  by_cases hsum : point.1 + point.2 = 3
  · obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_three_positive_gaps_have_radius
      point.1 point.2 (2-point.1) hxp hyp (by linarith)
    refine ⟨(radius,-radius),?_,?_,?_⟩
    · intro h; have hh := congrArg Prod.fst h; simpa using (ne_of_gt hr) hh
    · change sourceFeasible (point-(radius,-radius)); unfold sourceFeasible
      simp only [Prod.fst_sub,Prod.snd_sub]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change sourceFeasible (point+(radius,-radius)); unfold sourceFeasible
      simp only [Prod.fst_add,Prod.snd_add]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hsumlt : point.1 + point.2 < 3 := lt_of_le_of_ne hxy hsum
  obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_three_positive_gaps_have_radius
    point.1 (2-point.1) (3-point.1-point.2) hxp (by linarith) (by linarith)
  refine ⟨(radius,0),?_,?_,?_⟩
  · intro h; have hh := congrArg Prod.fst h; simpa using (ne_of_gt hr) hh
  · change sourceFeasible (point-(radius,0)); unfold sourceFeasible
    simp only [Prod.fst_sub,Prod.snd_sub]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · change sourceFeasible (point+(radius,0)); unfold sourceFeasible
    simp only [Prod.fst_add,Prod.snd_add]; exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_polygon_vertices_iff (point : ℝ × ℝ) :
    point ∈ sourcePolygon.extremePoints ℝ ↔
      point = (0,0) ∨ point = (2,0) ∨ point = (2,1) ∨ point = (0,3) := by
  constructor
  · intro hp
    by_contra hn
    push Not at hn
    obtain ⟨offset,hoff,hminus,hplus⟩ :=
      actual_unlisted_point_has_two_sided_feasible_perturbation point hp.1 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2
    have he := hp.2 hminus hplus (mem_openSegment_sub_add point offset)
    have hz : offset = 0 := by
      have hc := congrArg (fun value : ℝ × ℝ => point-value) he
      simpa using hc
    exact hoff hz
  · rintro (rfl|rfl|rfl|rfl)
    · exact actual_vertex_0_is_extreme
    · exact actual_vertex_1_is_extreme
    · exact actual_vertex_2_is_extreme
    · exact actual_vertex_3_is_extreme

theorem actual_disallowed_corner : ((3,0) : ℝ × ℝ) ∉ sourcePolygon := by
  norm_num [sourcePolygon,sourceFeasible]

theorem actual_source_vertex_objective_values :
    sourceObjective (0,0) = 0 ∧ sourceObjective (2,0) = 4 ∧
    sourceObjective (2,1) = 5 ∧ sourceObjective (0,3) = 3 := by
  norm_num [sourceObjective]

theorem actual_whole_set_bound_and_unique_equality (point : ℝ × ℝ)
    (hp : point ∈ sourcePolygon) :
    sourceObjective point = point.1 + (point.1 + point.2) ∧
      sourceObjective point ≤ 5 ∧ (sourceObjective point = 5 ↔ point = (2,1)) := by
  rcases hp with ⟨hx,hy,hxy,hx2⟩
  refine ⟨by unfold sourceObjective; ring,by unfold sourceObjective; linarith,?_⟩
  constructor
  · intro he
    unfold sourceObjective at he
    apply Prod.ext <;> change _ = _ <;> linarith
  · intro he; subst point; norm_num [sourceObjective]

theorem actual_unique_global_maximum :
    (2,1) ∈ sourcePolygon ∧
      ∀ point ∈ sourcePolygon, sourceObjective point ≤ sourceObjective (2,1) ∧
        (sourceObjective point = sourceObjective (2,1) ↔ point = (2,1)) := by
  refine ⟨by norm_num [sourcePolygon,sourceFeasible],?_⟩
  intro point hp
  norm_num [sourceObjective]
  exact (actual_whole_set_bound_and_unique_equality point hp).2

end SafeLearning.CompleteFoundationsPolygonLP
