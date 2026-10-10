import SafeLearning.CompleteAppliedPendulumLinear
import SafeLearning.CompleteAppliedGlobalLipschitzTrajectory

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SafeLearning.CompleteAppliedPendulumLocalField
open SafeLearning.CompleteAppliedPendulumLinear

def clamp (q:ℝ) : ℝ := max (-1/10) (min (1/10) q)
def residual (q:ℝ) : ℝ := 10*(clamp q-Real.sin (clamp q))
def auxiliaryField (x:ℝ×ℝ) : ℝ×ℝ := (x.2,-10*x.1-x.2/10+residual x.1)
def hangingField (x:ℝ×ℝ) : ℝ×ℝ := (x.2,-10*Real.sin x.1-x.2/10)
def storage (x:ℝ×ℝ) : ℝ := 10*x.1^2+x.2^2+x.1*x.2/20
def storageRate (x:ℝ×ℝ) : ℝ :=
  20*x.1*x.2+2*x.2*(auxiliaryField x).2+
    ((x.2)^2+x.1*(auxiliaryField x).2)/20

theorem actual_clamp_bounds_and_identity (q:ℝ) :
    |clamp q|≤1/10 ∧ |clamp q|≤|q| ∧ (|q|≤1/10 → clamp q=q) := by
  have hl : (-1/10:ℝ)≤clamp q := le_max_left _ _
  have hu : clamp q≤(1/10:ℝ) := max_le (by norm_num) (min_le_left _ _)
  refine ⟨abs_le.mpr ⟨by linarith,hu⟩,?_,?_⟩
  · by_cases hq : q<(-1/10:ℝ)
    · have he : clamp q= -1/10 := by unfold clamp;rw [min_eq_right (by linarith),max_eq_left hq.le]
      rw [he,abs_of_nonpos (by norm_num),abs_of_neg (by linarith)]
      linarith
    · by_cases hq' : (1/10:ℝ)<q
      · have he : clamp q=1/10 := by unfold clamp;rw [min_eq_left hq'.le,max_eq_right (by norm_num)]
        rw [he,abs_of_nonneg (by norm_num),abs_of_pos (by linarith)]
        linarith
      · have he : clamp q=q := by unfold clamp;rw [min_eq_right (le_of_not_gt hq'),max_eq_right (le_of_not_gt hq)]
        rw [he]
  · intro hq
    unfold clamp
    rw [min_eq_right (abs_le.mp hq).2,max_eq_right (by linarith [(abs_le.mp hq).1])]

theorem actual_clamped_nonlinear_residual_is_globally_small (q:ℝ) :
    |residual q|≤|q|/10 := by
  have hc:=actual_clamp_bounds_and_identity q
  have hs:=Real.abs_sub_sin_le (clamp q)
  have ha:=abs_nonneg (clamp q)
  have hsq : |clamp q|^2≤(1/100:ℝ) := by nlinarith [hc.1]
  have hcube : |clamp q|^3≤|clamp q|/100 := by
    have h:=mul_le_mul_of_nonneg_left hsq ha
    nlinarith
  rw [residual,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<10)]
  nlinarith [hc.2.1]

theorem actual_auxiliary_field_agrees_with_source_near_hanging (x:ℝ×ℝ)
    (hx:|x.1|≤1/10) :
    auxiliaryField x=hangingField x ∧ field (x.1+Real.pi,x.2)=hangingField x := by
  have he:clamp x.1=x.1:=(actual_clamp_bounds_and_identity x.1).2.2 hx
  constructor
  · apply Prod.ext <;> simp [auxiliaryField,hangingField,residual,he] <;> ring
  · apply Prod.ext <;> simp [field,hangingField,Real.sin_add] <;> ring

theorem actual_local_storage_has_global_positive_quadratic_bounds (x:ℝ×ℝ) :
    (2/5:ℝ)*(x.1^2+x.2^2)≤ storage x ∧
      storage x≤11*(x.1^2+x.2^2) := by
  unfold storage
  constructor <;> nlinarith [sq_nonneg (x.1+x.2),sq_nonneg (x.1-x.2),
    sq_nonneg x.1,sq_nonneg x.2]

theorem actual_auxiliary_storage_derivative_has_a_uniform_negative_rate (x:ℝ×ℝ) :
    storageRate x≤-(1/1000:ℝ)*storage x := by
  have hr:=actual_clamped_nonlinear_residual_is_globally_small x.1
  have hvr : 2*x.2*residual x.1≤(x.1^2+x.2^2)/10 := by
    have hprod : x.2*residual x.1≤|x.2| *(|x.1|/10) := by
      calc
        _≤|x.2*residual x.1|:=le_abs_self _
        _=|x.2| *|residual x.1|:=abs_mul _ _
        _≤|x.2| *(|x.1|/10):=mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    nlinarith [sq_nonneg (|x.1|-|x.2|),sq_abs x.1,sq_abs x.2]
  have hqr : x.1*residual x.1≤x.1^2/10 := by
    calc
      _≤|x.1*residual x.1|:=le_abs_self _
      _=|x.1| *|residual x.1|:=abs_mul _ _
      _≤|x.1| *(|x.1|/10):=mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _=x.1^2/10:=by rw [←mul_div_assoc,←pow_two,sq_abs]
  dsimp [storageRate,storage,auxiliaryField]
  nlinarith [sq_nonneg (x.1+x.2),sq_nonneg (x.1-x.2),sq_nonneg x.1,sq_nonneg x.2]

theorem actual_auxiliary_field_is_globally_lipschitz : LipschitzWith (301/10) auxiliaryField := by
  have hc : LipschitzWith 1 clamp := (LipschitzWith.id.const_min (1/10)).const_max (-1/10)
  have hs : LipschitzWith 1 (fun q=>Real.sin (clamp q)) := by simpa only [one_mul,Function.comp_def] using Real.lipschitzWith_sin.comp hc
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hq : |x.1-y.1|≤‖x-y‖ := by simpa only [Real.norm_eq_abs,Prod.fst_sub] using norm_fst_le (x-y)
  have hv : |x.2-y.2|≤‖x-y‖ := by simpa only [Real.norm_eq_abs,Prod.snd_sub] using norm_snd_le (x-y)
  have hz : |clamp x.1-clamp y.1|≤|x.1-y.1| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hc.dist_le_mul x.1 y.1
  have hsin : |Real.sin (clamp x.1)-Real.sin (clamp y.1)|≤|x.1-y.1| := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using hs.dist_le_mul x.1 y.1
  have hr : |residual x.1-residual y.1|≤20*|x.1-y.1| := by
    calc
      _=10*|(clamp x.1-clamp y.1)-(Real.sin (clamp x.1)-Real.sin (clamp y.1))| := by
        unfold residual
        calc
          _=|10*((clamp x.1-clamp y.1)-(Real.sin (clamp x.1)-Real.sin (clamp y.1)))| := by congr 1;ring
          _=10*|(clamp x.1-clamp y.1)-(Real.sin (clamp x.1)-Real.sin (clamp y.1))| := by rw [abs_mul];norm_num
      _≤10*(|clamp x.1-clamp y.1|+|Real.sin (clamp x.1)-Real.sin (clamp y.1)|) := by
        gcongr;exact abs_sub _ _
      _≤20*|x.1-y.1| := by linarith
  have ha : |(auxiliaryField x).2-(auxiliaryField y).2|≤(301/10:ℝ)*‖x-y‖ := by
    calc
      _=|(-10*(x.1-y.1)-(x.2-y.2)/10)+(residual x.1-residual y.1)| := by
        unfold auxiliaryField;congr 1;ring
      _≤|-10*(x.1-y.1)-(x.2-y.2)/10|+|residual x.1-residual y.1|:=abs_add_le _ _
      _≤10*|x.1-y.1|+|x.2-y.2|/10+20*|x.1-y.1| := by
        have hb:=abs_sub (-10*(x.1-y.1)) ((x.2-y.2)/10)
        norm_num [abs_mul,abs_div] at hb
        simp only [neg_mul] at hb ⊢
        linarith
      _≤(301/10:ℝ)*‖x-y‖ := by linarith
  rw [dist_eq_norm,Prod.norm_def]
  change max |(auxiliaryField x).1-(auxiliaryField y).1|
    |(auxiliaryField x).2-(auxiliaryField y).2|≤(301/10:ℝ)*‖x-y‖
  apply max_le
  · change |x.2-y.2|≤_
    nlinarith [norm_nonneg (x-y)]
  · exact ha

end SafeLearning.CompleteAppliedPendulumLocalField
