import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace SafeLearning.CompleteFoundationsMetricDefinitions22

variable {E : Type*} [NormedAddCommGroup E]

theorem actual_open_and_closed_balls_are_the_literal_norm_sets (point : E) (radius : ℝ) :
    Metric.ball point radius={value | ‖value-point‖<radius} ∧
      Metric.closedBall point radius={value | ‖value-point‖≤radius} := by
  constructor <;>ext value <;>simp [Metric.mem_ball,Metric.mem_closedBall,dist_eq_norm]

theorem actual_interior_points_are_exactly_the_positive_radius_ball_certificates
    (set : Set E) (point : E) :
    point ∈ interior set ↔ ∃ radius : ℝ,0<radius ∧ {value | ‖value-point‖<radius} ⊆ set := by
  rw [mem_interior_iff_mem_nhds,Metric.mem_nhds_iff]
  simp only [Metric.ball,dist_eq_norm]

theorem actual_open_sets_equal_their_interior_and_closed_sets_have_open_complements
    (set : Set E) :
    (IsOpen set ↔ set=interior set) ∧ (IsClosed set ↔ IsOpen setᶜ) := by
  exact ⟨interior_eq_iff_isOpen.symm.trans eq_comm,isClosed_iff_compl_open⟩

theorem actual_closed_sets_are_exactly_the_sets_containing_all_their_sequence_limits
    (set : Set E) :
    IsClosed set ↔ ∀ (sequence : ℕ → E) (point : E),
      (∀ n,sequence n ∈ set) → Tendsto sequence atTop (𝓝 point) → point ∈ set := by
  constructor
  · intro hclosed sequence point hsequence hlimit
    exact hclosed.mem_of_tendsto hlimit (Eventually.of_forall hsequence)
  · intro hlimits
    exact IsSeqClosed.isClosed (fun sequence point hsequence hlimit =>
      hlimits sequence point hsequence hlimit)

theorem actual_metric_closure_is_exactly_the_set_of_limits_of_sequences_in_the_set
    (set : Set E) (point : E) :
    point ∈ closure set ↔ ∃ sequence : ℕ → E,
      (∀ n,sequence n ∈ set) ∧ Tendsto sequence atTop (𝓝 point) :=
  mem_closure_iff_seq_limit

theorem actual_frontier_is_closure_minus_interior_and_every_ball_meets_both_sides
    (set : Set E) (point : E) :
    frontier set=closure set\interior set ∧
      (point ∈ frontier set ↔ ∀ radius : ℝ,0<radius →
        (Metric.ball point radius∩set).Nonempty ∧
        (Metric.ball point radius∩setᶜ).Nonempty) := by
  refine ⟨rfl,?_⟩
  rw [frontier_eq_closure_inter_closure]
  simp only [mem_inter_iff,Metric.mem_closure_iff]
  constructor
  · rintro ⟨hset,hcomplement⟩ radius hradius
    obtain ⟨inside,hinside,hdinside⟩ := hset radius hradius
    obtain ⟨outside,houtside,hdoutside⟩ := hcomplement radius hradius
    exact ⟨⟨inside,⟨by simpa [Metric.mem_ball,dist_comm] using hdinside,hinside⟩⟩,
      ⟨outside,⟨by simpa [Metric.mem_ball,dist_comm] using hdoutside,houtside⟩⟩⟩
  · intro hballs
    constructor <;>intro radius hradius
    · obtain ⟨inside,hball,hinside⟩ := (hballs radius hradius).1
      exact ⟨inside,hinside,by simpa [Metric.mem_ball,dist_comm] using hball⟩
    · obtain ⟨outside,hball,houtside⟩ := (hballs radius hradius).2
      exact ⟨outside,houtside,by simpa [Metric.mem_ball,dist_comm] using hball⟩

theorem actual_neighborhoods_are_exactly_sets_containing_some_positive_radius_ball
    (set : Set E) (point : E) :
    set ∈ 𝓝 point ↔ ∃ radius : ℝ,0<radius ∧ {value | ‖value-point‖<radius} ⊆ set := by
  rw [Metric.mem_nhds_iff]
  simp only [Metric.ball,dist_eq_norm]

theorem actual_literal_half_open_interval_has_the_printed_interior_closure_and_boundary :
    interior (Ico (0:ℝ) 1)=Ioo (0:ℝ) 1 ∧
      closure (Ico (0:ℝ) 1)=Icc (0:ℝ) 1 ∧
      frontier (Ico (0:ℝ) 1)={(0:ℝ),1} :=
  ⟨interior_Ico,closure_Ico (by norm_num),frontier_Ico (by norm_num)⟩

theorem actual_literal_half_open_interval_is_neither_open_nor_closed :
    ¬IsOpen (Ico (0:ℝ) 1) ∧ ¬IsClosed (Ico (0:ℝ) 1) := by
  constructor
  · intro hopen
    have heq := hopen.interior_eq
    rw [interior_Ico] at heq
    have hzero : (0:ℝ)∈Ico (0:ℝ) 1 := by norm_num
    rw [←heq] at hzero
    norm_num at hzero
  · intro hclosed
    have heq := hclosed.closure_eq
    rw [closure_Ico (by norm_num : (0:ℝ)≠1)] at heq
    have hone : (1:ℝ)∈Icc (0:ℝ) 1 := by norm_num
    rw [heq] at hone
    norm_num at hone

end SafeLearning.CompleteFoundationsMetricDefinitions22
