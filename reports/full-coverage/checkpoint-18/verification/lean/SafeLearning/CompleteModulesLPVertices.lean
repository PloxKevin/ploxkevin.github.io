import SafeLearning.CompleteModulesLinearProgram

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Set
namespace SafeLearning.CompleteModulesLPVertices
open CompleteModulesLinearProgram

def actualLPPrimalSet : Set (ℝ×ℝ) := {point | actualLPPrimalFeasible point.1 point.2}
def actualLPDualSet : Set (ℝ×ℝ) := {point | actualLPDualFeasible point.1 point.2}

theorem actual_positive_numbers_have_a_common_strict_radius (first second third : ℝ)
    (hf : 0 < first) (hs : 0 < second) (ht : 0 < third) :
    ∃ radius : ℝ,0 < radius ∧ radius<first ∧ radius<second ∧ radius<third := by
  refine ⟨min first (min second third)/2,?_,?_,?_,?_⟩
  · exact div_pos (lt_min hf (lt_min hs ht)) (by norm_num)
  · have h := min_le_left first (min second third);linarith
  · have h := (min_le_right first (min second third)).trans (min_le_left second third);linarith
  · have h := (min_le_right first (min second third)).trans (min_le_right second third);linarith

theorem actual_two_sided_nonzero_feasible_perturbation_excludes_extremeness
    (domain : Set (ℝ×ℝ)) (point offset : ℝ×ℝ) (hoffset : offset≠0)
    (hminus : point-offset∈domain) (hplus : point+offset∈domain) :
    point∉domain.extremePoints ℝ := by
  intro h
  have he := h.2 hminus hplus (mem_openSegment_sub_add point offset)
  have hz : offset=0 := by
    have hc := congrArg (fun value : ℝ×ℝ => point-value) he
    simpa using hc
  exact hoffset hz

theorem actual_unlisted_primal_points_have_feasible_nonzero_perturbations
    (first second : ℝ) (hfeasible : actualLPPrimalFeasible first second)
    (hfirstVertex : (first,second)≠((6,0):ℝ×ℝ))
    (hsecondVertex : (first,second)≠((0,4):ℝ×ℝ))
    (hthirdVertex : (first,second)≠((3,1):ℝ×ℝ)) :
    ∃ offset : ℝ×ℝ,offset≠0 ∧ (first,second)-offset∈actualLPPrimalSet ∧
      (first,second)+offset∈actualLPPrimalSet := by
  rcases hfeasible with ⟨hf,hs,hone,htwo⟩
  by_cases hz : first=0
  · have hg : 4<second := by
      have hn : second≠4 := by intro he;exact hsecondVertex (by simp [hz,he])
      exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_positive_numbers_have_a_common_strict_radius
      second (second-4) 1 (by linarith) (by linarith) (by norm_num)
    refine ⟨(0,radius),?_,?_,?_⟩
    · intro he;have hh:=congrArg Prod.snd he;simpa using (ne_of_gt hr) hh
    · change actualLPPrimalFeasible (first-0) (second-radius)
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPPrimalFeasible (first+0) (second+radius)
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  by_cases hzSecond : second=0
  · have hg : 6<first := by
      have hn : first≠6 := by intro he;exact hfirstVertex (by simp [hzSecond,he])
      exact lt_of_le_of_ne (by linarith) (Ne.symm hn)
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_positive_numbers_have_a_common_strict_radius
      first (first-6) 1 (by linarith) (by linarith) (by norm_num)
    refine ⟨(radius,0),?_,?_,?_⟩
    · intro he;have hh:=congrArg Prod.fst he;simpa using (ne_of_gt hr) hh
    · change actualLPPrimalFeasible (first-radius) (second-0)
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPPrimalFeasible (first+radius) (second+0)
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hfp : 0 < first := lt_of_le_of_ne hf (Ne.symm hz)
  have hsp : 0 < second := lt_of_le_of_ne hs (Ne.symm hzSecond)
  by_cases he : first+second=4
  · have hstrict : 6<first+3*second := by
      by_contra hn
      have hp : first=3 ∧ second=1 := by constructor <;> linarith
      exact hthirdVertex (by simp [hp.1,hp.2])
    obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
      first second ((first+3*second-6)/2) hfp hsp (by linarith)
    refine ⟨(radius,-radius),?_,?_,?_⟩
    · intro hx;have hh:=congrArg Prod.fst hx;simpa using (ne_of_gt hr) hh
    · change actualLPPrimalFeasible (first-radius) (second-(-radius))
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPPrimalFeasible (first+radius) (second+(-radius))
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hstrict : 4<first+second := lt_of_le_of_ne hone (Ne.symm he)
  by_cases heSecond : first+3*second=6
  · obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
      (first/3) second ((first+second-4)/2) (by linarith) hsp (by linarith)
    refine ⟨(3*radius,-radius),?_,?_,?_⟩
    · intro hx;have hh:=congrArg Prod.fst hx
      change 3*radius=0 at hh;linarith
    · change actualLPPrimalFeasible (first-3*radius) (second-(-radius))
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPPrimalFeasible (first+3*radius) (second+(-radius))
      unfold actualLPPrimalFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hstrictSecond : 6<first+3*second := lt_of_le_of_ne htwo (Ne.symm heSecond)
  obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
    first (first+second-4) (first+3*second-6) hfp (by linarith) (by linarith)
  refine ⟨(radius,0),?_,?_,?_⟩
  · intro hx;have hh:=congrArg Prod.fst hx;simpa using (ne_of_gt hr) hh
  · change actualLPPrimalFeasible (first-radius) (second-0)
    unfold actualLPPrimalFeasible
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · change actualLPPrimalFeasible (first+radius) (second+0)
    unfold actualLPPrimalFeasible
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_unlisted_dual_points_have_feasible_nonzero_perturbations
    (first second : ℝ) (hfeasible : actualLPDualFeasible first second)
    (hzeroVertex : (first,second)≠((0,0):ℝ×ℝ))
    (hfirstVertex : (first,second)≠((2,0):ℝ×ℝ))
    (hsecondVertex : (first,second)≠((0,1):ℝ×ℝ))
    (hthirdVertex : (first,second)≠((3/2,1/2):ℝ×ℝ)) :
    ∃ offset : ℝ×ℝ,offset≠0 ∧ (first,second)-offset∈actualLPDualSet ∧
      (first,second)+offset∈actualLPDualSet := by
  rcases hfeasible with ⟨hf,hs,hone,htwo⟩
  by_cases hz : first=0
  · have hsp : 0 < second := by
      have hn : second≠0 := by intro he;exact hzeroVertex (by simp [hz,he])
      exact lt_of_le_of_ne hs (Ne.symm hn)
    have hg : second<1 := by
      have hn : second≠1 := by intro he;exact hsecondVertex (by simp [hz,he])
      exact lt_of_le_of_ne (by linarith) hn
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_positive_numbers_have_a_common_strict_radius
      second (1-second) 1 hsp (by linarith) (by norm_num)
    refine ⟨(0,radius),?_,?_,?_⟩
    · intro he;have hh:=congrArg Prod.snd he;simpa using (ne_of_gt hr) hh
    · change actualLPDualFeasible (first-0) (second-radius)
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPDualFeasible (first+0) (second+radius)
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  by_cases hzSecond : second=0
  · have hfp : 0 < first := lt_of_le_of_ne hf (Ne.symm hz)
    have hg : first<2 := by
      have hn : first≠2 := by intro he;exact hfirstVertex (by simp [hzSecond,he])
      exact lt_of_le_of_ne (by linarith) hn
    obtain ⟨radius,hr,hra,hrb,_⟩ := actual_positive_numbers_have_a_common_strict_radius
      first (2-first) 1 hfp (by linarith) (by norm_num)
    refine ⟨(radius,0),?_,?_,?_⟩
    · intro he;have hh:=congrArg Prod.fst he;simpa using (ne_of_gt hr) hh
    · change actualLPDualFeasible (first-radius) (second-0)
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPDualFeasible (first+radius) (second+0)
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hfp : 0 < first := lt_of_le_of_ne hf (Ne.symm hz)
  have hsp : 0 < second := lt_of_le_of_ne hs (Ne.symm hzSecond)
  by_cases he : first+second=2
  · have hstrict : first+3*second<3 := by
      by_contra hn
      have hp : first=3/2 ∧ second=1/2 := by constructor <;> linarith
      exact hthirdVertex (by simp [hp.1,hp.2])
    obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
      first second ((3-first-3*second)/2) hfp hsp (by linarith)
    refine ⟨(radius,-radius),?_,?_,?_⟩
    · intro hx;have hh:=congrArg Prod.fst hx;simpa using (ne_of_gt hr) hh
    · change actualLPDualFeasible (first-radius) (second-(-radius))
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPDualFeasible (first+radius) (second+(-radius))
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hstrict : first+second<2 := lt_of_le_of_ne hone he
  by_cases heSecond : first+3*second=3
  · obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
      (first/3) second ((2-first-second)/2) (by linarith) hsp (by linarith)
    refine ⟨(3*radius,-radius),?_,?_,?_⟩
    · intro hx;have hh:=congrArg Prod.fst hx
      change 3*radius=0 at hh;linarith
    · change actualLPDualFeasible (first-3*radius) (second-(-radius))
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
    · change actualLPDualFeasible (first+3*radius) (second+(-radius))
      unfold actualLPDualFeasible
      exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  have hstrictSecond : first+3*second<3 := lt_of_le_of_ne htwo heSecond
  obtain ⟨radius,hr,hra,hrb,hrc⟩ := actual_positive_numbers_have_a_common_strict_radius
    first (2-first-second) (3-first-3*second) hfp (by linarith) (by linarith)
  refine ⟨(radius,0),?_,?_,?_⟩
  · intro hx;have hh:=congrArg Prod.fst hx;simpa using (ne_of_gt hr) hh
  · change actualLPDualFeasible (first-radius) (second-0)
    unfold actualLPDualFeasible
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · change actualLPDualFeasible (first+radius) (second+0)
    unfold actualLPDualFeasible
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero
    (left right first second : ℝ) (hl : 0 < left) (hr : 0 < right)
    (hf : 0 ≤ first) (hs : 0 ≤ second) (hz : left*first+right*second=0) :
    first=0 ∧ second=0 := by
  have hlf : left*first=0 := le_antisymm (by linarith [mul_nonneg hr.le hs]) (mul_nonneg hl.le hf)
  have hrs : right*second=0 := le_antisymm (by linarith [mul_nonneg hl.le hf]) (mul_nonneg hr.le hs)
  exact ⟨(mul_eq_zero.mp hlf).resolve_left (ne_of_gt hl),
    (mul_eq_zero.mp hrs).resolve_left (ne_of_gt hr)⟩

theorem actual_primal_first_listed_vertex_is_extreme :
    ((6,0) : ℝ×ℝ)∈actualLPPrimalSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPPrimalSet,actualLPPrimalFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=6 at hx
  change left*firstPoint.2+right*secondPoint.2=0 at hy
  have hgap0 : firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.2) (secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : firstPoint.1+3*firstPoint.2-6=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1+3*firstPoint.2-6) (secondPoint.1+3*secondPoint.2-6) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=6;linarith
  · change firstPoint.2=0;linarith

theorem actual_primal_second_listed_vertex_is_extreme :
    ((0,4) : ℝ×ℝ)∈actualLPPrimalSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPPrimalSet,actualLPPrimalFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=0 at hx
  change left*firstPoint.2+right*secondPoint.2=4 at hy
  have hgap0 : firstPoint.1=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1) (secondPoint.1) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : firstPoint.1+firstPoint.2-4=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1+firstPoint.2-4) (secondPoint.1+secondPoint.2-4) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=0;linarith
  · change firstPoint.2=4;linarith

theorem actual_primal_third_listed_vertex_is_extreme :
    ((3,1) : ℝ×ℝ)∈actualLPPrimalSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPPrimalSet,actualLPPrimalFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=3 at hx
  change left*firstPoint.2+right*secondPoint.2=1 at hy
  have hgap0 : firstPoint.1+firstPoint.2-4=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1+firstPoint.2-4) (secondPoint.1+secondPoint.2-4) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : firstPoint.1+3*firstPoint.2-6=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1+3*firstPoint.2-6) (secondPoint.1+3*secondPoint.2-6) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=3;linarith
  · change firstPoint.2=1;linarith

theorem actual_dual_zero_listed_vertex_is_extreme :
    ((0,0) : ℝ×ℝ)∈actualLPDualSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPDualSet,actualLPDualFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=0 at hx
  change left*firstPoint.2+right*secondPoint.2=0 at hy
  have hgap0 : firstPoint.1=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1) (secondPoint.1) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.2) (secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=0;linarith
  · change firstPoint.2=0;linarith

theorem actual_dual_first_listed_vertex_is_extreme :
    ((2,0) : ℝ×ℝ)∈actualLPDualSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPDualSet,actualLPDualFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=2 at hx
  change left*firstPoint.2+right*secondPoint.2=0 at hy
  have hgap0 : firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.2) (secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : 2-firstPoint.1-firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (2-firstPoint.1-firstPoint.2) (2-secondPoint.1-secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=2;linarith
  · change firstPoint.2=0;linarith

theorem actual_dual_second_listed_vertex_is_extreme :
    ((0,1) : ℝ×ℝ)∈actualLPDualSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPDualSet,actualLPDualFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=0 at hx
  change left*firstPoint.2+right*secondPoint.2=1 at hy
  have hgap0 : firstPoint.1=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (firstPoint.1) (secondPoint.1) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : 3-firstPoint.1-3*firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (3-firstPoint.1-3*firstPoint.2) (3-secondPoint.1-3*secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=0;linarith
  · change firstPoint.2=1;linarith

theorem actual_dual_third_listed_vertex_is_extreme :
    ((3/2,1/2) : ℝ×ℝ)∈actualLPDualSet.extremePoints ℝ := by
  apply mem_extremePoints_iff_left.mpr
  refine ⟨by norm_num [actualLPDualSet,actualLPDualFeasible],?_⟩
  intro firstPoint hfirst secondPoint hsecond hsegment
  rcases hfirst with ⟨hff,hfs,hfone,hftwo⟩
  rcases hsecond with ⟨hsf,hss,hsone,hstwo⟩
  rcases hsegment with ⟨left,right,hl,hr,hsum,hpoint⟩
  have hx := congrArg Prod.fst hpoint
  have hy := congrArg Prod.snd hpoint
  change left*firstPoint.1+right*secondPoint.1=3/2 at hx
  change left*firstPoint.2+right*secondPoint.2=1/2 at hy
  have hgap0 : 2-firstPoint.1-firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (2-firstPoint.1-firstPoint.2) (2-secondPoint.1-secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  have hgap1 : 3-firstPoint.1-3*firstPoint.2=0 :=
    (actual_positive_weight_zero_sum_forces_each_nonnegative_term_zero left right
      (3-firstPoint.1-3*firstPoint.2) (3-secondPoint.1-3*secondPoint.2) hl hr (by linarith) (by linarith)
      (by nlinarith only [hx,hy,hsum])).1
  apply Prod.ext
  · change firstPoint.1=3/2;linarith
  · change firstPoint.2=1/2;linarith

theorem actual_primal_extreme_points_are_exactly_the_three_reported_vertices
    (point : ℝ×ℝ) :
    point∈actualLPPrimalSet.extremePoints ℝ ↔
      point=(6,0) ∨ point=(0,4) ∨ point=(3,1) := by
  constructor
  · intro h
    by_contra hvertices
    push Not at hvertices
    obtain ⟨offset,hoffset,hminus,hplus⟩ :=
      actual_unlisted_primal_points_have_feasible_nonzero_perturbations point.1 point.2
        h.1 hvertices.1 hvertices.2.1 hvertices.2.2
    exact actual_two_sided_nonzero_feasible_perturbation_excludes_extremeness
      actualLPPrimalSet point offset hoffset hminus hplus h
  · rintro (rfl|rfl|rfl)
    · exact actual_primal_first_listed_vertex_is_extreme
    · exact actual_primal_second_listed_vertex_is_extreme
    · exact actual_primal_third_listed_vertex_is_extreme

theorem actual_dual_extreme_points_are_exactly_the_four_reported_vertices
    (point : ℝ×ℝ) :
    point∈actualLPDualSet.extremePoints ℝ ↔
      point=(0,0) ∨ point=(2,0) ∨ point=(0,1) ∨ point=(3/2,1/2) := by
  constructor
  · intro h
    by_contra hvertices
    push Not at hvertices
    obtain ⟨offset,hoffset,hminus,hplus⟩ :=
      actual_unlisted_dual_points_have_feasible_nonzero_perturbations point.1 point.2
        h.1 hvertices.1 hvertices.2.1 hvertices.2.2.1 hvertices.2.2.2
    exact actual_two_sided_nonzero_feasible_perturbation_excludes_extremeness
      actualLPDualSet point offset hoffset hminus hplus h
  · rintro (rfl|rfl|rfl|rfl)
    · exact actual_dual_zero_listed_vertex_is_extreme
    · exact actual_dual_first_listed_vertex_is_extreme
    · exact actual_dual_second_listed_vertex_is_extreme
    · exact actual_dual_third_listed_vertex_is_extreme

end SafeLearning.CompleteModulesLPVertices
