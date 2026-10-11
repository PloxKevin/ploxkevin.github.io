import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace SafeLearning.CompleteModulesGoSafeBackupGeometry

/-- A genuine continuous path with the four printed samples and an unsafe intersample peak. -/
def sourceSamplePath (t : ℝ) : ℝ :=
  (3/10)*t+(13/10)*max 0 (t-1)-2*max 0 (t-3/2)-
    (1/10)*max 0 (t-2)+(1/2)*max 0 (t-3)
def sourceMargin (x : ℝ) : ℝ := 1-|x|
def sourceSamples (i : Fin 4) : ℝ := sourceSamplePath i

theorem actual_continuous_source_path_has_every_printed_sample_and_unsafe_peak :
    Continuous sourceSamplePath ∧ sourceSamplePath 0=0 ∧ sourceSamplePath 1=3/10 ∧
      sourceSamplePath 2=9/10 ∧ sourceSamplePath 3=2/5 ∧ sourceSamplePath (3/2)=11/10 := by
  constructor
  · unfold sourceSamplePath
    fun_prop
  · norm_num [sourceSamplePath]

theorem actual_sampled_margin_is_least_point_one_but_full_path_is_unsafe :
    IsLeast (Set.range (fun i : Fin 4=>sourceMargin (sourceSamples i))) (1/10) ∧
    (∀ i : Fin 4,0 ≤ sourceMargin (sourceSamples i)) ∧
    sourceMargin (sourceSamplePath (3/2))=-(1/10) ∧
    ¬ (∀ t : ℝ,0 ≤ t→0 ≤ sourceMargin (sourceSamplePath t)) := by
  have hp := actual_continuous_source_path_has_every_printed_sample_and_unsafe_peak
  constructor
  · constructor
    · exact ⟨2,by norm_num [sourceSamples,sourceSamplePath,sourceMargin]⟩
    · rintro m ⟨i,rfl⟩
      fin_cases i <;> norm_num [sourceSamples,sourceSamplePath,sourceMargin]
  constructor
  · intro i
    fin_cases i <;> norm_num [sourceSamples,sourceSamplePath,sourceMargin]
  constructor
  · norm_num [sourceSamplePath,sourceMargin]
  · intro h
    have hc := h (3/2) (by norm_num)
    norm_num [sourceSamplePath,sourceMargin] at hc

theorem actual_positive_lipschitz_backup_test_is_exactly_the_radius_test
    (x center lower motion L : ℝ) (hL : 0<L) :
    L*(|x-center|+motion) ≤ lower ↔ |x-center| ≤ lower/L-motion := by
  rw [mul_comm L,←le_div_iff₀ hL]
  constructor <;> intro h <;> linarith

theorem actual_negative_radius_certifies_no_scalar_state
    (center radius : ℝ) (hr : radius<0) :
    {x : ℝ | |x-center| ≤ radius}=∅ := by
  ext x
  simp only [Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
  intro h
  linarith [abs_nonneg (x-center)]

theorem actual_scalar_backup_ball_and_printed_point :
    (3/5:ℝ)/2-1/20=1/4 ∧
      {x : ℝ | |x-1/5| ≤ (3/5)/2-1/20}=Icc (-(1/20)) (9/20) ∧
      (2/5:ℝ)∈{x : ℝ | |x-1/5| ≤ (3/5)/2-1/20} ∧
      (3/5:ℝ)-2*(|2/5-1/5|+1/20)=1/10 := by
  constructor
  · norm_num
  constructor
  · ext x
    simp only [Set.mem_setOf_eq,Set.mem_Icc]
    have hr : (3/5:ℝ)/2-1/20=1/4 := by norm_num
    rw [hr,abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
  norm_num

def sourceBackupUnion : Set ℝ := Icc (-(2/5)) (1/10)∪Icc (3/10) (7/10)

theorem actual_backup_union_covers_only_the_printed_witnesses_and_retains_its_gap :
    (0:ℝ)∈sourceBackupUnion ∧ (1/5:ℝ)∉sourceBackupUnion ∧
      (1/2:ℝ)∈sourceBackupUnion ∧
      sourceBackupUnion⊆Icc (-(2/5)) (7/10) ∧
      Ioo (1/10:ℝ) (3/10)∩sourceBackupUnion=∅ ∧
      ¬ (Icc (-(2/5):ℝ) (7/10)⊆sourceBackupUnion) := by
  constructor
  · norm_num [sourceBackupUnion]
  constructor
  · norm_num [sourceBackupUnion]
  constructor
  · norm_num [sourceBackupUnion]
  constructor
  · intro x hx
    rcases hx with hx|hx <;> constructor <;> linarith [hx.1,hx.2]
  constructor
  · ext x
    simp only [Set.mem_inter_iff,Set.mem_Ioo,sourceBackupUnion,Set.mem_union,Set.mem_Icc,
      Set.mem_empty_iff_false,iff_false]
    rintro ⟨hx,hfirst|hsecond⟩
    · linarith [hx.1,hfirst.2]
    · linarith [hx.2,hsecond.1]
  · intro h
    have hx := h (show (1/5:ℝ)∈Icc (-(2/5)) (7/10) by norm_num)
    norm_num [sourceBackupUnion] at hx

theorem actual_inside_approximation_preserves_every_certified_state_property
    {X : Type*} (certified approximate : Set X) (safe : X→Prop)
    (hinner : approximate⊆certified) (hcertified : ∀ x∈certified,safe x) :
    ∀ x∈approximate,safe x := fun x hx=>hcertified x (hinner hx)

theorem actual_parameter_state_cartesian_grid_counts (dimension : ℕ) :
    Fintype.card (Fin 100×(Fin dimension→Fin 10))=100*10^dimension := by simp

theorem actual_two_six_dimensions_and_one_more_coordinate_counts :
    Fintype.card (Fin 100×(Fin 2→Fin 10))=10000 ∧
      Fintype.card (Fin 100×(Fin 6→Fin 10))=100000000 ∧
      (∀ dimension : ℕ,Fintype.card (Fin 100×(Fin (dimension+1)→Fin 10))=
        10*Fintype.card (Fin 100×(Fin dimension→Fin 10))) := by
  simp only [actual_parameter_state_cartesian_grid_counts]
  constructor
  · norm_num
  constructor
  · norm_num
  · intro dimension
    rw [pow_succ]
    ring

end SafeLearning.CompleteModulesGoSafeBackupGeometry
