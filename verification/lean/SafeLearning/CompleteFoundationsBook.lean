import SafeLearning.PrimersFoundations
import SafeLearning.BookApplications

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

/-! Full algebraic model statements for the twelve application exercises in
Primers 0, A and B. Physical calibration, units and timing are model assumptions,
not empirical consequences of these theorems. -/
namespace SafeLearning.CompleteFoundationsBook

theorem measurement_interval_exact (y ε lo hi : ℝ) (hε : 0 ≤ ε) :
    (∀ x : ℝ, |x-y| ≤ ε → x ∈ Icc lo hi) ↔
      lo ≤ y-ε ∧ y+ε ≤ hi := by
  constructor
  · intro h
    have hlow := (h (y-ε) (by simp [abs_of_nonneg hε])).1
    have hhigh := (h (y+ε) (by simp [abs_of_nonneg hε])).2
    exact ⟨hlow,hhigh⟩
  · rintro ⟨hlow,hhigh⟩ x hx
    have hab := abs_le.mp hx
    constructor <;> linarith [hab.1,hab.2]

theorem temperature_reading_rule (y : ℝ) :
    (∀ x : ℝ, |x-y| ≤ 1/5 → x ∈ Icc 0 5) ↔ y ∈ Icc (1/5) (24/5) := by
  rw [measurement_interval_exact y (1/5) 0 5 (by norm_num)]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem reading_examples :
    (47/10 : ℝ) ∈ Icc (1/5) (24/5) ∧
    (49/10 : ℝ) ∉ Icc (1/5) (24/5) ∧
    |(47/10 : ℝ)-49/10| ≤ 1/5 ∧ (47/10 : ℝ) ∈ Icc 0 5 ∧
    |(51/10 : ℝ)-49/10| ≤ 1/5 ∧ (51/10 : ℝ) ∉ Icc 0 5 := by norm_num

theorem chamber_command_exact (x u d : ℝ) (hd : 0 ≤ d) :
    (∀ w ∈ Icc (0 : ℝ) d, 11/10*x+u+w ∈ Icc 0 5) ↔
      0 ≤ 11/10*x+u ∧ 11/10*x+u+d ≤ 5 := by
  constructor
  · intro h
    exact ⟨by simpa using (h 0 ⟨le_rfl,hd⟩).1,(h d ⟨hd,le_rfl⟩).2⟩
  · rintro ⟨hlo,hhi⟩ w hw
    constructor <;> linarith [hw.1,hw.2]

theorem chamber_exercise_commands (u : ℝ) :
    (u ∈ Icc (-1 : ℝ) 0 ∧ ∀ w ∈ Icc (0 : ℝ) (2/5),
      11/10*(24/5)+u+w ∈ Icc 0 5) ↔ u ∈ Icc (-1 : ℝ) (-17/25) := by
  rw [chamber_command_exact _ _ _ (by norm_num)]
  constructor
  · rintro ⟨hu,h⟩; constructor <;> linarith [hu.1,hu.2,h.1,h.2]
  · intro hu; exact ⟨⟨hu.1,by linarith [hu.2]⟩,by constructor <;> linarith [hu.1,hu.2]⟩

theorem chamber_worked_commands (u : ℝ) :
    (u ∈ Icc (-1 : ℝ) 0 ∧ ∀ w ∈ Icc (0 : ℝ) (2/5),
      11/10*(9/2)+u+w ∈ Icc 0 5) ↔ u ∈ Icc (-1 : ℝ) (-7/20) := by
  rw [chamber_command_exact _ _ _ (by norm_num)]
  constructor
  · rintro ⟨hu,h⟩; constructor <;> linarith [hu.1,hu.2,h.1,h.2]
  · intro hu; exact ⟨⟨hu.1,by linarith [hu.2]⟩,by constructor <;> linarith [hu.1,hu.2]⟩

theorem anticipative_command (w : ℝ) (hw : w ∈ Icc (0 : ℝ) (2/5)) :
    -7/25-w ∈ Icc (-17/25 : ℝ) (-7/25) ∧
      11/10*(24/5)+(-7/25-w)+w=5 := by
  constructor
  · constructor <;> linarith [hw.1,hw.2]
  · ring

theorem chamber_nominal_feedback (x w : ℝ)
    (hx : x ∈ Icc (0 : ℝ) 5) (hw : w ∈ Icc (0 : ℝ) (2/5)) :
    -9/50*x ∈ Icc (-1 : ℝ) 0 ∧ 11/10*x+(-9/50*x)+w ∈ Icc 0 5 := by
  constructor <;> constructor <;> linarith [hx.1,hx.2,hw.1,hw.2]

theorem chamber_no_fixed_command :
    ¬ ∃ u : ℝ, ∀ x ∈ Icc (0 : ℝ) 5, ∀ w ∈ Icc (0 : ℝ) (2/5),
      11/10*x+u+w ∈ Icc 0 5 := by
  rintro ⟨u,h⟩
  have hlo := (h 0 (by norm_num) 0 (by norm_num)).1
  have hhi := (h 5 (by norm_num) (2/5) (by norm_num)).2
  linarith

theorem chamber_feedback_range (d : ℝ) (hd : 0 ≤ d) :
    (∀ x ∈ Icc (0 : ℝ) 5, ∃ u ∈ Icc (-1 : ℝ) 0,
      ∀ w ∈ Icc (0 : ℝ) d, 11/10*x+u+w ∈ Icc 0 5) ↔ d ≤ 1/2 := by
  constructor
  · intro h
    obtain ⟨u,hu,hs⟩ := h 5 (by norm_num)
    have hhi := (hs d ⟨hd,le_rfl⟩).2
    linarith [hu.1]
  · intro h x hx
    refine ⟨-x/5,?_,?_⟩
    · constructor <;> linarith [hx.1,hx.2]
    · intro w hw; constructor <;> linarith [hx.1,hx.2,hw.1,hw.2]

theorem chamber_invariance (x w : ℕ → ℝ) (d : ℝ)
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1/2) (hzero : x 0 ∈ Icc (0 : ℝ) 5)
    (hw : ∀ n, w n ∈ Icc (0 : ℝ) d)
    (hstep : ∀ n, x (n+1)=11/10*x n-x n/5+w n) :
    ∀ n, x n ∈ Icc (0 : ℝ) 5 := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
    rw [hstep]
    constructor <;> linarith [ih.1,ih.2,(hw n).1,(hw n).2]

theorem affine_recurrence_envelope (e : ℕ → ℝ) (q c b : ℝ)
    (hq : 0 ≤ q) (hb : q*b+c=b) (hstep : ∀ n, e (n+1) ≤ q*e n+c) :
    ∀ n, e n ≤ b+q^n*(e 0-b) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := mul_le_mul_of_nonneg_left ih hq
    have hs := hstep n
    rw [pow_succ]
    nlinarith

theorem affine_recurrence_realization (q b a : ℝ) (n : ℕ) :
    b+q^(n+1)*(a-b)=q*(b+q^n*(a-b))+(1-q)*b := by rw [pow_succ]; ring

theorem exercise_error_envelope (e : ℕ → ℝ) (hzero : e 0=7/10)
    (hstep : ∀ n, e (n+1) ≤ (1/2)*e n+3/100) :
    ∀ n, e n ≤ 3/50+16/25*(1/2)^n := by
  intro n
  have hh := affine_recurrence_envelope e (1/2) (3/100) (3/50) (by norm_num) (by norm_num) hstep n
  rw [hzero] at hh
  convert hh using 1 <;> ring

theorem error_exercise_minimal_index (n : ℕ) :
    (3/50+16/25*(1/2 : ℝ)^n ≤ 7/100 ↔ 6 ≤ n) ∧
    (3/50+16/25*(1/2 : ℝ)^n < 7/100 ↔ 7 ≤ n) := by
  have hmono : Antitone (fun k : ℕ => (1/2 : ℝ)^k) := pow_right_anti₀ (by norm_num) (by norm_num)
  constructor <;> constructor
  · intro h; by_contra hn
    have hn' : n ≤ 5 := by omega
    have hh := hmono hn'; norm_num at hh; linarith
  · intro hn; have hh := hmono hn; norm_num at hh; linarith
  · intro h; by_contra hn
    have hn' : n ≤ 6 := by omega
    have hh := hmono hn'; norm_num at hh; linarith
  · intro hn; have hh := hmono hn; norm_num at hh; linarith

theorem error_floor_unattainable (n : ℕ) :
    3/50 < 3/50+16/25*(1/2 : ℝ)^n ∧
    ¬ (3/50+16/25*(1/2 : ℝ)^n ≤ 1/25) := by
  have hp : 0 < (1/2 : ℝ)^n := pow_pos (by norm_num) _
  constructor <;> nlinarith

theorem worked_error_budget (n : ℕ) :
    (1/20+3/4*(3/5 : ℝ)^n ≤ 3/50 ↔ 9 ≤ n) := by
  have hmono : Antitone (fun k : ℕ => (3/5 : ℝ)^k) := pow_right_anti₀ (by norm_num) (by norm_num)
  constructor
  · intro h; by_contra hn
    have hn' : n ≤ 8 := by omega
    have hh := hmono hn'; norm_num at hh; linarith
  · intro hn; have hh := hmono hn; norm_num at hh; linarith

theorem balanced_reconstruction (y₁ y₂ z₁ z₂ : ℝ) :
    (z₁+z₂=y₁ ∧ z₁-z₂=y₂) ↔ z₁=(y₁+y₂)/2 ∧ z₂=(y₁-y₂)/2 := by
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem balanced_error_geometry (η₁ η₂ ε : ℝ)
    (h₁ : |η₁| ≤ ε) (h₂ : |η₂| ≤ ε) :
    |(η₁+η₂)/2| ≤ ε ∧
    ((η₁+η₂)/2)^2+((η₁-η₂)/2)^2 ≤ ε^2 := by
  have hε : 0 ≤ ε := (abs_nonneg η₁).trans h₁
  have ha := abs_le.mp h₁
  have hb := abs_le.mp h₂
  constructor
  · apply abs_le.mpr; constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  · have hs₁ : η₁^2 ≤ ε^2 := by nlinarith [ha.1,ha.2]
    have hs₂ : η₂^2 ≤ ε^2 := by nlinarith [hb.1,hb.2]
    nlinarith

theorem sum_measurement_all_solutions (x y : ℝ) :
    x+y=6 ↔ ∃ t : ℝ, x=3+t ∧ y=3-t := by
  constructor
  · intro h; exact ⟨x-3,by ring,by linarith⟩
  · rintro ⟨t,rfl,rfl⟩; ring

theorem sum_measurement_identification (t : ℝ) :
    (3+t)^2+(3-t)^2=18+2*t^2 ∧
    ((3+t)^2+(3-t)^2=18 ↔ t=0) ∧
    (0 ≤ 3+t ∧ 0 ≤ 3-t ↔ t ∈ Icc (-3 : ℝ) 3) := by
  constructor
  · ring
  constructor
  · constructor <;> intro h <;> nlinarith [sq_nonneg t]
  · constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem sum_measurement_counterexample :
    (5 : ℝ)+1=6 ∧ (0 : ℝ) ≤ 5 ∧ (0 : ℝ) ≤ 1 ∧ (4 : ℝ)<5 := by norm_num

theorem sum_measurement_unique_minimum (x y : ℝ) (h : x+y=6) :
    18 ≤ x^2+y^2 ∧ (x^2+y^2=18 ↔ x=3 ∧ y=3) := by
  constructor
  · nlinarith [sq_nonneg (x-y)]
  · constructor
    · intro he; constructor <;> nlinarith [sq_nonneg (x-3),sq_nonneg (y-3)]
    · rintro ⟨rfl,rfl⟩; norm_num

theorem normalized_output_ball_bound (x y : ℝ) (h : x^2+y^2 ≤ (1/10)^2) :
    |2*x+y| ≤ Real.sqrt 5/10 := by
  have hs := SafeLearning.PrimersFoundations.cauchy_schwarz_two 2 1 x y
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hp := Real.sqrt_nonneg (5 : ℝ)
  apply abs_le.mpr; constructor <;> nlinarith [sq_nonneg (2*x+y)]

theorem normalized_output_attainer :
    (2/(10*Real.sqrt 5))^2+(1/(10*Real.sqrt 5))^2=(1/10 : ℝ)^2 ∧
    2*(2/(10*Real.sqrt 5))+1/(10*Real.sqrt 5)=Real.sqrt 5/10 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hn : Real.sqrt (5 : ℝ) ≠ 0 := by positivity
  constructor <;> field_simp <;> nlinarith

theorem normalized_box_bound (x y : ℝ) (hx : |x| ≤ 1/10) (hy : |y| ≤ 1/10) :
    |2*x+y| ≤ 3/10 := by
  have ha := abs_le.mp hx
  have hb := abs_le.mp hy
  exact abs_le.mpr ⟨by linarith [ha.1,hb.1],by linarith [ha.2,hb.2]⟩

theorem normalized_output_decimal_bound :
    (223606/1000000 : ℝ)<Real.sqrt 5/10 ∧ Real.sqrt 5/10<(223608/1000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤5)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith

def sensorLoss (x y : ℝ) : ℝ :=
  (x+y-6)^2+(x+11/10*y-31/5)^2+(y-21/10)^2

theorem three_sensor_loss_identity (x y : ℝ) :
    sensorLoss x y = sensorLoss (261/67) (422/201)+
      ((x-261/67)+(y-422/201))^2+
      ((x-261/67)+11/10*(y-422/201))^2+(y-422/201)^2 := by
  unfold sensorLoss; ring

theorem three_sensor_unique_optimum (x y : ℝ) :
    sensorLoss (261/67) (422/201) ≤ sensorLoss x y ∧
    (sensorLoss x y = sensorLoss (261/67) (422/201) ↔ x=261/67 ∧ y=422/201) := by
  have hi := three_sensor_loss_identity x y
  constructor
  · nlinarith [sq_nonneg ((x-261/67)+(y-422/201)),
      sq_nonneg ((x-261/67)+11/10*(y-422/201)),sq_nonneg (y-422/201)]
  · constructor
    · intro h
      have hy : y=422/201 := by
        nlinarith [sq_nonneg ((x-261/67)+(y-422/201)),
          sq_nonneg ((x-261/67)+11/10*(y-422/201)),sq_nonneg (y-422/201)]
      subst y
      constructor
      · nlinarith [sq_nonneg (x-261/67)]
      · rfl
    · rintro ⟨rfl,rfl⟩; rfl

theorem three_sensor_residual_certificate :
    (6 : ℝ)-(261/67+422/201)=1/201 ∧
    (31/5 : ℝ)-(261/67+11/10*(422/201))= -1/201 ∧
    (21/10 : ℝ)-422/201=1/2010 ∧
    (1/201 : ℝ)+(-1/201)=0 ∧
    (1/201 : ℝ)+11/10*(-1/201)+1/2010=0 ∧
    ((261/67 : ℝ)-4)^2+(422/201-2)^2=(29/201)^2 := by norm_num

def allocationCost (u v : ℝ) : ℝ := ((u-3)^2+4*(v-1)^2)/2
def allocationU (b : ℝ) : ℝ := (4*b-1)/5
def allocationV (b : ℝ) : ℝ := (b+1)/5
def allocationMultiplier (b : ℝ) : ℝ := 4*(4-b)/5
def allocationValue (b : ℝ) : ℝ := 2*(4-b)^2/5

theorem allocation_cost_identity (u v b : ℝ) :
    allocationCost u v = allocationValue b+
      ((u-allocationU b)^2+4*(v-allocationV b)^2)/2+
      allocationMultiplier b*(b-u-v) := by
  unfold allocationCost allocationValue allocationU allocationV allocationMultiplier; ring

theorem allocation_kkt (b : ℝ) (hb : b ∈ Ioo (1/4 : ℝ) 4) :
    0 < allocationU b ∧ 0 < allocationV b ∧
    allocationU b+allocationV b=b ∧ 0 < allocationMultiplier b ∧
    allocationU b-3+allocationMultiplier b=0 ∧
    4*(allocationV b-1)+allocationMultiplier b=0 ∧
    allocationMultiplier b*(allocationU b+allocationV b-b)=0 ∧
    allocationCost (allocationU b) (allocationV b)=allocationValue b := by
  unfold allocationU allocationV allocationMultiplier allocationCost allocationValue
  refine ⟨by linarith [hb.1],by linarith [hb.1],by ring,by linarith [hb.2],by ring,by ring,by ring,by ring⟩

theorem allocation_unique_optimum (u v b : ℝ) (hb : b ≤ 4) (hbudget : u+v ≤ b) :
    allocationValue b ≤ allocationCost u v ∧
    (allocationCost u v=allocationValue b ↔ u=allocationU b ∧ v=allocationV b) := by
  have hi := allocation_cost_identity u v b
  have hmul : 0 ≤ allocationMultiplier b*(b-u-v) := by
    apply mul_nonneg
    · unfold allocationMultiplier; linarith
    · linarith
  unfold allocationCost allocationValue allocationU allocationV allocationMultiplier at *
  constructor
  · nlinarith [sq_nonneg (u-(4*b-1)/5),sq_nonneg (v-(b+1)/5)]
  · constructor
    · intro h
      constructor <;> nlinarith [sq_nonneg (u-(4*b-1)/5),sq_nonneg (v-(b+1)/5)]
    · rintro ⟨rfl,rfl⟩; ring

theorem allocation_value_derivative (b : ℝ) :
    HasDerivAt allocationValue (-allocationMultiplier b) b := by
  unfold allocationValue allocationMultiplier
  convert (((hasDerivAt_const b (4 : ℝ)).sub (hasDerivAt_id b)).pow 2).const_mul (2/5) using 1
  · ext x; dsimp; ring
  · dsimp; ring

theorem allocation_sensitivity_exact (b δ : ℝ) :
    allocationValue b-allocationValue (b+δ)=allocationMultiplier b*δ-2*δ^2/5 := by
  unfold allocationValue allocationMultiplier; ring

theorem allocation_transfer (t : ℝ) :
    allocationCost (12/5-t) (3/5+t)=1/2-t+5*t^2/2 ∧
    allocationCost (12/5-t) (3/5+t)=2/5+5*(t-1/5)^2/2 := by
  unfold allocationCost; constructor <;> ring

theorem sum_line_projection (x y b u v : ℝ) (h : u+v=b) :
    (u-x)^2+(v-y)^2 = (x+y-b)^2/2+
      2*(u-(x-(x+y-b)/2))^2 := by
  have hv : v=b-u := by linarith
  rw [hv]; ring

theorem allocation_numerical_checks :
    allocationU (5/2)=9/5 ∧ allocationV (5/2)=7/10 ∧
    allocationMultiplier (5/2)=6/5 ∧ allocationValue (5/2)=9/10 ∧
    allocationU (13/5)=47/25 ∧ allocationV (13/5)=18/25 ∧
    allocationMultiplier (13/5)=28/25 ∧ allocationValue (13/5)=98/125 ∧
    allocationValue (5/2)-allocationValue (13/5)=29/250 ∧
    (221/100 : ℝ)-3+4/5=1/100 ∧ 4*((4/5 : ℝ)-1)+4/5=0 ∧
    (221/100 : ℝ)+4/5-3=1/100 ∧
    (441/200 : ℝ)+(159/200)=3 ∧
    allocationCost (441/200) (159/200)=6401/16000 ∧
    allocationCost (441/200) (159/200)-allocationValue 3=1/16000 := by
  norm_num [allocationU,allocationV,allocationMultiplier,allocationValue,allocationCost]

def clearance (a w : ℝ) : ℝ := 3/10-a/5-a^2/10+w

theorem robust_clearance_exact (a d : ℝ) (hd : 0 ≤ d) :
    (∀ w : ℝ, |w| ≤ d → 1/10 ≤ clearance a w) ↔ (a+1)^2 ≤ 3-10*d := by
  unfold clearance
  constructor
  · intro h
    have hh := h (-d) (by simp [abs_of_nonneg hd])
    nlinarith
  · intro h w hw
    have hh := (abs_le.mp hw).1
    nlinarith

theorem robust_clearance_feasible (d : ℝ) (hd : 0 ≤ d) :
    (∃ a ∈ Icc (0 : ℝ) 1, ∀ w : ℝ, |w| ≤ d → 1/10 ≤ clearance a w) ↔ d ≤ 1/5 := by
  constructor
  · rintro ⟨a,ha,h⟩
    have hh := (robust_clearance_exact a d hd).1 h
    nlinarith [ha.1,sq_nonneg a]
  · intro h; refine ⟨0,by norm_num,?_⟩
    rw [robust_clearance_exact _ _ hd]
    norm_num; linarith

theorem clearance_optimum (d : ℝ) (hd : d ∈ Icc (0 : ℝ) (1/5)) :
    let s := Real.sqrt (3-10*d)
    s-1 ∈ Icc (0 : ℝ) 1 ∧
    clearance (s-1) (-d)=1/10 ∧
    ∀ a ∈ Icc (0 : ℝ) 1,
      (∀ w : ℝ, |w| ≤ d → 1/10 ≤ clearance a w) →
      (s-2)^2/2 ≤ (a-1)^2/2 ∧ ((a-1)^2/2=(s-2)^2/2 ↔ a=s-1) := by
  dsimp
  have harg : 0 ≤ 3-10*d := by linarith [hd.2]
  have hs := Real.sq_sqrt harg
  have hs₀ := Real.sqrt_nonneg (3-10*d)
  have hs₁ : 1 ≤ Real.sqrt (3-10*d) := by nlinarith [hd.2]
  have hs₂ : Real.sqrt (3-10*d) < 2 := by nlinarith [hd.1]
  refine ⟨⟨by linarith,by linarith⟩,?_,?_⟩
  · unfold clearance; nlinarith
  · intro a ha hf
    have hh := (robust_clearance_exact a d hd.1).1 hf
    have ha₁ : a ≤ Real.sqrt (3-10*d)-1 := by nlinarith [ha.1]
    constructor
    · nlinarith [ha.2]
    · constructor
      · intro he; nlinarith [ha.2]
      · intro he; rw [he]; ring

theorem clearance_kkt (d : ℝ) (hd : d ∈ Ico (0 : ℝ) (1/5)) :
    let s := Real.sqrt (3-10*d)
    let lam := (2-s)/(s/5)
    0 < s-1 ∧ s-1 < 1 ∧ 0 < lam ∧
    (s-1)-1+lam*((s-1)/5+1/5)=0 ∧
    lam*((s-1)^2/10+(s-1)/5-1/5+d)=0 := by
  dsimp
  have hs := Real.sq_sqrt (show 0 ≤ 3-10*d by linarith [hd.2])
  have hs₀ := Real.sqrt_nonneg (3-10*d)
  have hs₁ : 1 < Real.sqrt (3-10*d) := by nlinarith [hd.2]
  have hs₂ : Real.sqrt (3-10*d) < 2 := by nlinarith [hd.1]
  have hne : Real.sqrt (3-10*d) ≠ 0 := by linarith
  refine ⟨by linarith,by linarith,div_pos (by linarith) (by positivity),?_,?_⟩
  · field_simp; ring
  · have hz : (Real.sqrt (3-10*d)-1)^2/10+(Real.sqrt (3-10*d)-1)/5-1/5+d=0 := by nlinarith
    rw [hz,mul_zero]

theorem nonrobust_clearance_failure :
    clearance (Real.sqrt 3-1) 0=1/10 ∧
    clearance (Real.sqrt 3-1) (-3/100)=7/100 ∧ (7/100 : ℝ)<1/10 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  unfold clearance
  constructor
  · nlinarith
  constructor
  · nlinarith
  · norm_num

theorem chamber_exercise_numerics :
    (132/25 : ℝ)-4/5=112/25 ∧ (142/25 : ℝ)-4/5=122/25 ∧
    (99/20 : ℝ)-1/2=89/20 ∧ (107/20 : ℝ)-1/2=97/20 ∧
    (3/50 : ℝ)+16/25*(1/2)^5=2/25 ∧
    (3/50 : ℝ)+16/25*(1/2)^6=7/100 ∧
    (3/50 : ℝ)+16/25*(1/2)^7=13/200 ∧
    (5 : ℕ)+9*2=23 := by norm_num

theorem balanced_assembly_examples :
    ((1 : ℝ)+2=3 ∧ (1 : ℝ)-2= -1) ∧
    |(3 : ℝ)-((11/10)+2)| ≤ 1/10 ∧
    |(-1 : ℝ)-((11/10)-2)| ≤ 1/10 ∧ (21/20 : ℝ)<11/10 ∧
    (1 : ℝ)+1/25 ≤ 21/20 ∧
    (1/10 : ℝ)^2+(1/10)^2>(1/10)^2 := by norm_num

theorem balanced_stretch (x y : ℝ) :
    (x+y)^2+(x-y)^2=2*(x^2+y^2) := by ring

theorem nearparallel_reconstruction (a b x y : ℝ) :
    (x+y=a ∧ x+11/10*y=b) ↔ x=11*a-10*b ∧ y=10*(b-a) := by
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith

theorem nearparallel_error_example :
    (421/100 : ℝ)+9/5=601/100 ∧
    (421/100 : ℝ)+11/10*(9/5)=619/100 ∧
    ((421/100 : ℝ)-4)^2+(9/5-2)^2=(29/100)^2 := by norm_num

theorem sensor_gram_positive (x y : ℝ) :
    0 < 2*x^2+2*(21/10)*x*y+(321/100)*y^2 ↔ x ≠ 0 ∨ y ≠ 0 := by
  have he : 2*x^2+2*(21/10)*x*y+(321/100)*y^2=
    (x+y)^2+(x+11/10*y)^2+y^2 := by ring
  rw [he]
  constructor
  · intro h; by_contra hn; push_neg at hn; rcases hn with ⟨rfl,rfl⟩; norm_num at h
  · intro hn
    by_contra hh
    have hy : y=0 := by nlinarith [sq_nonneg (x+y),sq_nonneg (x+11/10*y),sq_nonneg y]
    subst y
    have hx : x=0 := by nlinarith [sq_nonneg x]
    exact hn.elim (fun h => h hx) (fun h => h rfl)

theorem least_squares_direction_derivative (x y p q : ℝ) :
    HasDerivAt (fun t : ℝ => sensorLoss (x+t*p) (y+t*q))
      (2*(x+y-6)*(p+q)+2*(x+11/10*y-31/5)*(p+11/10*q)+2*(y-21/10)*q) 0 := by
  have hx : HasDerivAt (fun t : ℝ => x+t*p) p 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const p).const_add x using 1 <;> simp
  have hy : HasDerivAt (fun t : ℝ => y+t*q) q 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).mul_const q).const_add y using 1 <;> simp
  unfold sensorLoss
  convert ((((hx.add hy).sub_const 6).pow 2).add
    (((hx.add (hy.const_mul (11/10))).sub_const (31/5)).pow 2)).add
    ((hy.sub_const (21/10)).pow 2) using 1 <;> norm_num <;> ring

theorem clearance_tangent_error (a : ℝ) :
    (3/10-a/5)-clearance a 0=a^2/10 ∧
    clearance 1 0=0 ∧ (3/10-(1 : ℝ)/5)=1/10 := by
  unfold clearance; constructor
  · ring
  · norm_num

theorem robust_clearance_decimal_bounds :
    (643167/1000000 : ℝ)<Real.sqrt (27/10)-1 ∧
    Real.sqrt (27/10)-1<(643169/1000000 : ℝ) ∧
    (63664/1000000 : ℝ)<(Real.sqrt (27/10)-2)^2/2 ∧
    (Real.sqrt (27/10)-2)^2/2<(63666/1000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤27/10)
  have hn := Real.sqrt_nonneg (27/10 : ℝ)
  have hlo : (1643167/1000000 : ℝ)<Real.sqrt (27/10) := by nlinarith
  have hhi : Real.sqrt (27/10)<(1643169/1000000 : ℝ) := by nlinarith
  refine ⟨by linarith,by linarith,?_,?_⟩ <;> nlinarith

theorem robust_multiplier_decimal_bound :
    (1085805/1000000 : ℝ)<(2-Real.sqrt (27/10))/(Real.sqrt (27/10)/5) ∧
    (2-Real.sqrt (27/10))/(Real.sqrt (27/10)/5)<1085808/1000000 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤27/10)
  have hn := Real.sqrt_nonneg (27/10 : ℝ)
  have hp : (0 : ℝ)<Real.sqrt (27/10)/5 := by positivity
  have hlo : (16431676/10000000 : ℝ)<Real.sqrt (27/10) := by nlinarith
  have hhi : Real.sqrt (27/10)<(16431678/10000000 : ℝ) := by nlinarith
  constructor
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

theorem nonrobust_clearance_decimal_bounds :
    (732050/1000000 : ℝ)<Real.sqrt 3-1 ∧ Real.sqrt 3-1<(732052/1000000 : ℝ) ∧
    (358983/10000000 : ℝ)<(7-4*Real.sqrt 3)/2 ∧
    (7-4*Real.sqrt 3)/2<(358985/10000000 : ℝ) ∧
    (773502/1000000 : ℝ)<10/Real.sqrt 3-5 ∧
    10/Real.sqrt 3-5<(773504/1000000 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hp : (0 : ℝ)<Real.sqrt 3 := by positivity
  have hlo : (173205080/100000000 : ℝ)<Real.sqrt 3 := by nlinarith
  have hhi : Real.sqrt 3<(173205081/100000000 : ℝ) := by nlinarith
  refine ⟨by linarith,by linarith,by linarith,by linarith,?_,?_⟩
  · have hh : (5773502/1000000 : ℝ)<10/Real.sqrt 3 := by rw [lt_div_iff₀ hp]; nlinarith
    linarith
  · have hh : 10/Real.sqrt 3<(5773504/1000000 : ℝ) := by rw [div_lt_iff₀ hp]; nlinarith
    linarith

theorem normal_equations_three_sensor :
    let H : Matrix (Fin 3) (Fin 2) ℝ := Matrix.of ![![1,1],![1,11/10],![0,1]]
    H.transpose*H=Matrix.of ![![2,21/10],![21/10,321/100]] ∧
    H.transpose.mulVec ![6,31/5,21/10]=![61/5,373/25] := by
  dsimp
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply,Fin.sum_univ_three]
  · ext i; fin_cases i <;>
      norm_num [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Matrix.of_apply,Fin.sum_univ_three]

theorem allocation_tangent_gradient (t : ℝ) :
    (-4/5 : ℝ)*(-t)+(-4/5)*t=0 ∧
    HasDerivAt (fun t : ℝ => allocationCost (12/5-t) (3/5+t)) (-1+5*t) t := by
  constructor
  · ring
  · have he : (fun t : ℝ => allocationCost (12/5-t) (3/5+t))=
        (fun t : ℝ => 1/2-t+5*t^2/2) := by
      ext x; exact (allocation_transfer x).1
    rw [he]
    convert (((hasDerivAt_const t (1/2 : ℝ)).sub (hasDerivAt_id t)).add
      ((((hasDerivAt_id t).pow 2).const_mul 5).div_const 2)) using 1 <;>
      (try funext z) <;> simp [Pi.add_apply,Pi.sub_apply,Pi.pow_apply,id_eq] <;> ring

end SafeLearning.CompleteFoundationsBook
