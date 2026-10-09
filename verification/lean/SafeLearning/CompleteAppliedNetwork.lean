import Mathlib
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedNetwork

def relu (z : ℝ) : ℝ := max 0 z
def score (z : ℝ) : ℝ := 6/5-(3/5)*relu (z+1/2)-(2/5)*relu (z-1/2)
def normalizedInput (y : ℝ) : ℝ := y-2

theorem relu_abs_bound (x y : ℝ) : |relu x-relu y| ≤ |x-y| := by
  have h := abs_max_sub_max_le_max (0:ℝ) x 0 y
  simpa [relu] using h

theorem score_abs_bound (x y : ℝ) : |score x-score y| ≤ |x-y| := by
  have h1 := relu_abs_bound (x+1/2) (y+1/2)
  have h2 := relu_abs_bound (x-1/2) (y-1/2)
  have he1 : x+1/2-(y+1/2)=x-y := by ring
  have he2 : x-1/2-(y-1/2)=x-y := by ring
  rw [he1] at h1
  rw [he2] at h2
  calc
    |score x-score y|=
      |-(3/5)*(relu (x+1/2)-relu (y+1/2))-(2/5)*(relu (x-1/2)-relu (y-1/2))| := by
        congr 1; unfold score; ring
    _ ≤ |-(3/5)*(relu (x+1/2)-relu (y+1/2))|+
        |(2/5)*(relu (x-1/2)-relu (y-1/2))| := abs_sub _ _
    _ = (3/5)*|relu (x+1/2)-relu (y+1/2)|+
        (2/5)*|relu (x-1/2)-relu (y-1/2)| := by rw [abs_mul,abs_mul]; norm_num
    _ ≤ |x-y| := by linarith

theorem nominal_score : score 0=9/10 := by norm_num [score,relu]

theorem normalized_error (y y0 : ℝ) :
    |normalizedInput y-normalizedInput y0|=|y-y0| := by unfold normalizedInput; congr 1; ring

theorem robust_nomination (y : ℝ) (hy : |y-2|≤1/5) :
    7/10 ≤ score (normalizedInput y) ∧ 0 < score (normalizedInput y) := by
  have hh := score_abs_bound (normalizedInput y) 0
  rw [nominal_score] at hh
  have he : |normalizedInput y-0|≤1/5 := by simpa [normalizedInput] using hy
  have hlo := (abs_le.mp hh).1
  constructor <;> linarith

theorem score_middle (z : ℝ) (hz : z ∈ Set.Icc (-1/2) (1/2)) :
    score z=9/10-(3/5)*z := by
  unfold score relu
  rw [max_eq_right (by linarith [hz.1]),max_eq_left (by linarith [hz.2])]
  ring

theorem nominal_interval_exact_minimum (z : ℝ) (hz : |z|≤1/5) :
    39/50 ≤ score z := by
  have hb := abs_le.mp hz
  rw [score_middle z (by constructor <;> linarith)]
  linarith [hb.2]

theorem nominal_interval_minimum_attained : score (1/5)=39/50 := by norm_num [score,relu]

theorem score_upper_piece (z : ℝ) (hz : 1/2≤z) : score z=11/10-z := by
  unfold score relu
  rw [max_eq_right (by linarith),max_eq_right (by linarith)]
  ring

theorem biased_nomination_values :
    normalizedInput (14/5)=4/5 ∧ score (4/5)=3/10 ∧
    score (23/20)=-(1/20) ∧ score (11/10)=0 ∧
    normalizedInput (31/10)=11/10 ∧ (31/10:ℝ)-14/5=3/10 := by
  norm_num [normalizedInput,score,relu]

theorem noise_bias_combination (noise bias : ℝ) (hn : |noise|≤1/5)
    (hb : |bias|≤3/20) : |noise+bias|≤7/20 := by
  exact (abs_add_le _ _).trans (by linarith)

theorem allowed_actual_flip : ∃ noise bias : ℝ,
    |noise|≤1/5 ∧ |bias|≤3/20 ∧
    score (normalizedInput (14/5)+noise+bias)<0 := by
  refine ⟨1/5,3/20,by norm_num,by norm_num,?_⟩
  norm_num [normalizedInput,score,relu]

theorem tie_distance_exact (delta : ℝ) (hd : 0≤delta) :
    (score (normalizedInput (14/5)+delta)>0 ↔ delta<3/10) ∧
    (score (normalizedInput (14/5)+delta)=0 ↔ delta=3/10) := by
  have hz : (1/2:ℝ)≤normalizedInput (14/5)+delta := by unfold normalizedInput; linarith
  rw [score_upper_piece _ hz]
  unfold normalizedInput
  constructor <;> constructor <;> intro h <;> linarith

/-- A zero-margin point prevents a strict-positive certificate on a closed ball. -/
theorem closed_interval_not_strictly_positive :
    ¬ (∀ z : ℝ, |z-4/5|≤7/20 → 0<score z) := by
  intro h
  have hh := h (11/10) (by norm_num)
  norm_num [score,relu] at hh

end SafeLearning.CompleteAppliedNetwork
