import Mathlib

set_option autoImplicit false
noncomputable section
open Set
open scoped Topology
namespace SafeLearning.CompleteFoundationsUniformDensityWhole30

theorem actual_closed_accuracy_characterizes_closure {E : Type*} [PseudoMetricSpace E]
    (G : Set E) (f : E) :
    f∈closure G ↔ ∀ ε : ℝ,0<ε→∃g∈G,dist f g≤ε := by
  constructor
  · intro h ε hε
    obtain ⟨g,hg,hd⟩:=Metric.mem_closure_iff.mp h ε hε
    exact ⟨g,hg,hd.le⟩
  · intro h
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨g,hg,hd⟩:=h (ε/2) (by positivity)
    exact ⟨g,hg,hd.trans_lt (by linarith)⟩

theorem actual_arbitrarily_good_uniform_class_approximation_iff {E : Type*} [PseudoMetricSpace E]
    (F G : Set E) :
    (∀f∈F,∀ε : ℝ,0<ε→∃g∈G,dist f g≤ε) ↔ F⊆closure G := by
  simp only [Set.subset_def,actual_closed_accuracy_characterizes_closure]

theorem actual_compact_sup_norm_bound_is_full_pointwise_bound {X : Type*}
    [TopologicalSpace X] [CompactSpace X] (f g : C(X,ℝ)) (ε : ℝ) (hε : 0≤ε) :
    ‖f-g‖≤ε ↔ ∀x : X,|f x-g x|≤ε := by
  simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs] using ContinuousMap.norm_le (f:=f-g) hε

theorem actual_compact_sup_norm_density_iff {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (F G : Set C(X,ℝ)) :
    (∀f∈F,∀ε : ℝ,0<ε→∃g∈G,∀x : X,|f x-g x|≤ε) ↔ F⊆closure G := by
  rw [←actual_arbitrarily_good_uniform_class_approximation_iff F G]
  apply forall_congr'
  intro f
  apply forall_congr'
  intro hf
  apply forall_congr'
  intro ε
  apply forall_congr'
  intro hε
  apply exists_congr
  intro g
  rw [←actual_compact_sup_norm_bound_is_full_pointwise_bound f g ε hε.le]
  simp only [dist_eq_norm]

def approximatingConstant (n : ℕ) : C(Unit,ℝ) := ContinuousMap.const Unit (1/((n : ℝ)+1))
def approximationClass : Set C(Unit,ℝ) := Set.range approximatingConstant
def targetClass : Set C(Unit,ℝ) := insert 0 approximationClass

theorem actual_constant_approximation_error (n : ℕ) :
    ‖(0 : C(Unit,ℝ))-approximatingConstant n‖=1/((n : ℝ)+1) := by
  rw [zero_sub,norm_neg]
  apply le_antisymm
  · apply (ContinuousMap.norm_le (f:=approximatingConstant n) (by positivity : 0≤1/((n : ℝ)+1))).mpr
    intro x
    simp only [approximatingConstant,ContinuousMap.const_apply,Real.norm_eq_abs]
    rw [abs_of_pos (by positivity : 0<1/((n : ℝ)+1))]
  · have h:=ContinuousMap.norm_coe_le_norm (approximatingConstant n) Unit.unit
    simpa only [approximatingConstant,ContinuousMap.const_apply,Real.norm_eq_abs,
      abs_of_pos (by positivity : 0<1/((n : ℝ)+1))] using h


theorem actual_zero_target_arbitrarily_uniformly_approximated :
    ∀ε : ℝ,0<ε→∃g∈approximationClass,‖(0 : C(Unit,ℝ))-g‖≤ε := by
  intro ε hε
  obtain ⟨n,hn⟩:=exists_nat_one_div_lt hε
  exact ⟨approximatingConstant n,⟨n,rfl⟩,(actual_constant_approximation_error n).trans_le hn.le⟩

theorem actual_dense_target_class_has_no_exact_zero_representative :
    targetClass⊆closure approximationClass ∧ (0 : C(Unit,ℝ))∈targetClass ∧
    (0 : C(Unit,ℝ))∉approximationClass := by
  refine ⟨?_,by simp [targetClass],?_⟩
  · intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl|hg
    · apply (actual_closed_accuracy_characterizes_closure approximationClass 0).mpr
      intro ε hε
      obtain ⟨g,hg,hd⟩:=actual_zero_target_arbitrarily_uniformly_approximated ε hε
      exact ⟨g,hg,by simpa [dist_eq_norm] using hd⟩
    · exact subset_closure hg
  · rintro ⟨n,hn⟩
    have h:=congrArg (fun f : C(Unit,ℝ)=>f Unit.unit) hn
    have hp : 0<1/((n : ℝ)+1) := by positivity
    simp [approximatingConstant] at h
    linarith


theorem actual_arbitrary_bounded_uniform_error_supremum_iff {X : Type*} [Nonempty X]
    (f g : X→ℝ) (hb : BddAbove (Set.range (fun x=>|f x-g x|))) (ε : ℝ) :
    sSup (Set.range (fun x=>|f x-g x|))≤ε ↔ ∀x,|f x-g x|≤ε := by
  constructor
  · intro h x
    exact (le_csSup hb (Set.mem_range_self x)).trans h
  · intro h
    apply csSup_le (Set.range_nonempty _)
    rintro y ⟨x,rfl⟩
    exact h x

theorem actual_arbitrary_bounded_sup_norm_density_condition_iff {X : Type*} [Nonempty X]
    (F G : Set (X→ℝ))
    (hb : ∀f∈F,∀g∈G,BddAbove (Set.range (fun x=>|f x-g x|))) :
    (∀f∈F,∀ε : ℝ,0<ε→∃g∈G,sSup (Set.range (fun x=>|f x-g x|))≤ε) ↔
    (∀f∈F,∀ε : ℝ,0<ε→∃g∈G,∀x,|f x-g x|≤ε) := by
  constructor
  · intro h f hf ε hε
    obtain ⟨g,hg,ha⟩:=h f hf ε hε
    exact ⟨g,hg,(actual_arbitrary_bounded_uniform_error_supremum_iff f g (hb f hf g hg) ε).mp ha⟩
  · intro h f hf ε hε
    obtain ⟨g,hg,ha⟩:=h f hf ε hε
    exact ⟨g,hg,(actual_arbitrary_bounded_uniform_error_supremum_iff f g (hb f hf g hg) ε).mpr ha⟩

end SafeLearning.CompleteFoundationsUniformDensityWhole30
