import SafeLearning.PrimersFoundations

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsGridExamples

def fineGrid : Set ℝ := {0,1/5,2/5,3/5,4/5,1}
def coarseGrid : Set ℝ := {0,2/5,4/5,1}

theorem fine_grid_covers (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ g ∈ fineGrid, |x-g| ≤ 1/10 := by
  by_cases h₀ : x ≤ 1/10
  · exact ⟨0,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith [hx.1]⟩
  by_cases h₁ : x ≤ 3/10
  · exact ⟨1/5,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith⟩
  by_cases h₂ : x ≤ 1/2
  · exact ⟨2/5,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith⟩
  by_cases h₃ : x ≤ 7/10
  · exact ⟨3/5,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith⟩
  by_cases h₄ : x ≤ 9/10
  · exact ⟨4/5,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith⟩
  exact ⟨1,by simp [fineGrid],by rw [abs_le]; constructor <;> linarith [hx.2]⟩

theorem coarse_grid_covers (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ g ∈ coarseGrid, |x-g| ≤ 1/5 := by
  by_cases h₀ : x ≤ 1/5
  · exact ⟨0,by simp [coarseGrid],by rw [abs_le]; constructor <;> linarith [hx.1]⟩
  by_cases h₁ : x ≤ 3/5
  · exact ⟨2/5,by simp [coarseGrid],by rw [abs_le]; constructor <;> linarith⟩
  exact ⟨4/5,by simp [coarseGrid],by rw [abs_le]; constructor <;> linarith [hx.2]⟩

theorem fine_grid_inside : fineGrid ⊆ Icc (0 : ℝ) 1 := by
  intro g hg
  simp only [fineGrid,mem_insert_iff,mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem coarse_grid_inside : coarseGrid ⊆ Icc (0 : ℝ) 1 := by
  intro g hg
  simp only [coarseGrid,mem_insert_iff,mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> norm_num

theorem exact_fine_grid_margin (h : ℝ → ℝ)
    (hh : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |h x-h y| ≤ 3*|x-y|)
    (hgrid : ∀ g ∈ fineGrid, 7/20 ≤ h g) :
    ∀ x ∈ Icc (0 : ℝ) 1, 1/20 ≤ h x := by
  intro x hx
  obtain ⟨g,hg,hd⟩ := fine_grid_covers x hx
  have hb := (abs_le.mp (hh x hx g (fine_grid_inside hg))).1
  linarith [hgrid g hg]

theorem exact_coarse_grid_margin (h : ℝ → ℝ)
    (hh : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |h x-h y| ≤ 3*|x-y|)
    (hgrid : ∀ g ∈ coarseGrid, 7/20 ≤ h g) :
    ∀ x ∈ Icc (0 : ℝ) 1, -(1/4) ≤ h x := by
  intro x hx
  obtain ⟨g,hg,hd⟩ := coarse_grid_covers x hx
  have hb := (abs_le.mp (hh x hx g (coarse_grid_inside hg))).1
  linarith [hgrid g hg]

theorem coarse_grid_midpoint_distance : Metric.infDist (1/5 : ℝ) coarseGrid=1/5 := by
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := (1/5 : ℝ))
      (by simp [coarseGrid] : (0 : ℝ) ∈ coarseGrid)
    norm_num [Real.dist_eq] at h
    exact h
  · apply (Metric.le_infDist (show coarseGrid.Nonempty from ⟨0,by simp [coarseGrid]⟩)).mpr
    intro y hy
    simp only [coarseGrid,mem_insert_iff,mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> norm_num [Real.dist_eq]

theorem fine_grid_midpoint_distance : Metric.infDist (1/10 : ℝ) fineGrid=1/10 := by
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := (1/10 : ℝ))
      (by simp [fineGrid] : (0 : ℝ) ∈ fineGrid)
    norm_num [Real.dist_eq] at h
    exact h
  · apply (Metric.le_infDist (show fineGrid.Nonempty from ⟨0,by simp [fineGrid]⟩)).mpr
    intro y hy
    simp only [fineGrid,mem_insert_iff,mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [Real.dist_eq]

def coarseCounterexample (x : ℝ) : ℝ := 7/20-3*Metric.infDist x coarseGrid

theorem coarse_counterexample_lipschitz (x y : ℝ) :
    |coarseCounterexample x-coarseCounterexample y| ≤ 3*|x-y| := by
  have h := SafeLearning.PrimersFoundations.distance_to_set_lipschitz coarseGrid x y
  rw [Real.dist_eq] at h
  have he : coarseCounterexample x-coarseCounterexample y=
      -3*(Metric.infDist x coarseGrid-Metric.infDist y coarseGrid) := by
    dsimp [coarseCounterexample]; ring
  rw [he,abs_mul]; norm_num
  linarith

theorem coarse_counterexample_samples (g : ℝ) (hg : g ∈ coarseGrid) :
    coarseCounterexample g=7/20 := by
  have hzero : Metric.infDist g coarseGrid=0 := by
    apply le_antisymm
    · simpa using Metric.infDist_le_dist_of_mem (x := g) hg
    · exact Metric.infDist_nonneg
  simp [coarseCounterexample,hzero]

theorem coarse_counterexample_failure :
    (1/5 : ℝ) ∈ Icc (0 : ℝ) 1 ∧ coarseCounterexample (1/5)= -(1/4) := by
  norm_num [coarseCounterexample,coarse_grid_midpoint_distance]

theorem reciprocal_budget_iff (T : ℕ) (hT : 1 ≤ T) :
    (8 : ℝ)/(T : ℝ) ≤ 1/10 ↔ 80 ≤ T := by
  have hp : (0 : ℝ)<T := by exact_mod_cast (show 0<T by omega)
  rw [div_le_iff₀ hp]
  constructor
  · intro h; have h' : (80 : ℝ) ≤ T := by linarith
    exact_mod_cast h'
  · intro h; have h' : (80 : ℝ) ≤ T := by exact_mod_cast h
    linarith

theorem square_root_budget_iff (T : ℕ) (hT : 1 ≤ T) :
    (4 : ℝ)/Real.sqrt (T : ℝ) ≤ 1/10 ↔ 1600 ≤ T := by
  have hp : (0 : ℝ)<T := by exact_mod_cast (show 0<T by omega)
  have hsp : 0<Real.sqrt (T : ℝ) := Real.sqrt_pos.mpr hp
  have hsq := Real.sq_sqrt hp.le
  rw [div_le_iff₀ hsp]
  constructor
  · intro h; have h' : (1600 : ℝ) ≤ T := by nlinarith
    exact_mod_cast h'
  · intro h; have h' : (1600 : ℝ) ≤ T := by exact_mod_cast h
    nlinarith [Real.sqrt_nonneg (T : ℝ)]

theorem exact_budget_comparison :
    (1600 : ℕ)*100=160000 ∧ (80 : ℕ)*1000=80000 ∧
      (80 : ℕ)*1000*2=1600*100 ∧ (1000 : ℕ)=10*100 := by norm_num

theorem geometric_accuracy_log_iff (q e₀ ε : ℝ) (n : ℕ)
    (hq₀ : 0<q) (hq₁ : q<1) (he : 0<e₀) (hε : 0<ε) :
    q^n*e₀ ≤ ε ↔ Real.log (e₀/ε)/Real.log (1/q) ≤ (n : ℝ) := by
  have hqlog : Real.log q < 0 := Real.log_neg hq₀ hq₁
  have hinvlog : 0<Real.log (1/q) := by rw [one_div,Real.log_inv]; linarith
  rw [← Real.log_le_log_iff (mul_pos (pow_pos hq₀ n) he) hε,
    Real.log_mul (pow_ne_zero n hq₀.ne') he.ne',Real.log_pow,
    div_le_iff₀ hinvlog,Real.log_div he.ne' hε.ne',one_div,Real.log_inv]
  constructor <;> intro h <;> linarith

end SafeLearning.CompleteFoundationsGridExamples
