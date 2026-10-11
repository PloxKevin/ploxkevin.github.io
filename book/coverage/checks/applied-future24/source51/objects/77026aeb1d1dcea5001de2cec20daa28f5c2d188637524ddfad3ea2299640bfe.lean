import SafeLearning.CompleteFoundationsTaylorModels

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Matrix
open scoped BigOperators Topology

namespace SafeLearning.CompleteFoundationsTaylorCheck
abbrev E := EuclideanSpace ℝ (Fin 2)
open CompleteFoundationsSpectralModels (point applyMatrix matrix_coordinate_action inner_coordinate_formula)
open CompleteFoundationsCalculusModels (coordinate)

def objective (x : E) : ℝ := (x 0)^2*x 1+Real.exp (x 1)
def sourceGradient (x : E) : E := point (2*x 0*x 1) ((x 0)^2+Real.exp (x 1))
def sourceHessian (x : E) : Matrix (Fin 2) (Fin 2) ℝ := !![2*x 1,2*x 0;2*x 0,Real.exp (x 1)]
def base : E := point 1 0
def firstModel (delta : E) : ℝ := 1+2*delta 1
def secondModel (delta : E) : ℝ := 1+2*delta 1+2*delta 0*delta 1+(delta 1)^2/2
def remainder (delta : E) : ℝ := objective (base+delta)-secondModel delta

theorem actual_gradient (x : E) : HasGradientAt objective (sourceGradient x) x := by
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  have hf : HasFDerivAt objective ((2*x 0*x 1) • coordinate 0+((x 0)^2+Real.exp (x 1)) • coordinate 1) x := by
    convert ((h0.pow 2).mul h1).add h1.exp using 1
    · rfl
    · ext u
      simp [coordinate,PiLp.proj,PiLp.projₗ]
      ring
  rw [hasGradientAt_iff_hasFDerivAt]
  convert hf using 1
  ext u
  simp [sourceGradient,point,coordinate,InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply,Fin.sum_univ_succ,PiLp.proj,PiLp.projₗ]
  ring

theorem actual_hessian (x : E) :
    HasFDerivAt (gradient objective) (applyMatrix (sourceHessian x)) x := by
  have he : gradient objective=(fun z : E => (2*z 0*z 1) • point 1 0+((z 0)^2+Real.exp (z 1)) • point 0 1) := by
    funext z
    rw [(actual_gradient z).gradient]
    ext i
    fin_cases i <;> simp [sourceGradient,point]
  rw [he]
  have h0 := (coordinate 0).hasFDerivAt (x := x)
  have h1 := (coordinate 1).hasFDerivAt (x := x)
  convert (((h0.const_mul 2).mul h1).smul_const (point 1 0)).add
    (((h0.pow 2).add h1.exp).smul_const (point 0 1)) using 1
  · rfl
  · ext u i
    rw [matrix_coordinate_action]
    fin_cases i <;> simp [coordinate,sourceHessian,point,PiLp.proj,PiLp.projₗ]
    all_goals ring

theorem actual_source_gradient_directional_and_hessian :
    objective base=1 ∧ gradient objective base=point 0 2 ∧
    fderiv ℝ objective base (point (3/5) (4/5))=8/5 ∧
    sourceHessian base=!![0,2;2,1] ∧ (sourceHessian base).det= -4 := by
  rw [(actual_gradient base).gradient,(actual_gradient base).fderiv_apply,inner_coordinate_formula]
  norm_num [objective,base,sourceGradient,sourceHessian,point,Matrix.det_fin_two]

theorem actual_source_first_and_second_taylor_models (delta : E) :
    firstModel delta=objective base+inner ℝ (gradient objective base) delta ∧
    secondModel delta=firstModel delta+(1/2:ℝ)*inner ℝ delta (applyMatrix (sourceHessian base) delta) := by
  rw [actual_source_gradient_directional_and_hessian.1,
    actual_source_gradient_directional_and_hessian.2.1,inner_coordinate_formula]
  constructor
  · simp [firstModel,point]
  · rw [matrix_coordinate_action,inner_coordinate_formula]
    simp [secondModel,firstModel,sourceHessian,base,point]
    ring

theorem actual_source_characteristic_polynomial (value : ℝ) :
    (sourceHessian base-value • (1:Matrix (Fin 2) (Fin 2) ℝ)).det=value^2-value-4 := by
  simp [sourceHessian,base,point,Matrix.det_fin_two]
  ring

theorem actual_source_characteristic_roots (value : ℝ) :
    (sourceHessian base-value • (1:Matrix (Fin 2) (Fin 2) ℝ)).det=0 ↔
      value=(1+Real.sqrt 17)/2 ∨ value=(1-Real.sqrt 17)/2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤17)
  have he : value^2-value-4=(value-(1+Real.sqrt 17)/2)*(value-(1-Real.sqrt 17)/2) := by
    nlinarith
  rw [actual_source_characteristic_polynomial,he,mul_eq_zero]
  simp only [sub_eq_zero]

theorem actual_each_source_eigenvalue_has_a_nonzero_eigenvector
    (value : ℝ) (hv : value=(1+Real.sqrt 17)/2 ∨ value=(1-Real.sqrt 17)/2) :
    (![2,value] : Fin 2 → ℝ)≠0 ∧
      sourceHessian base *ᵥ ![2,value]=value • (![2,value] : Fin 2 → ℝ) := by
  have hroot := (actual_source_characteristic_roots value).mpr hv
  rw [actual_source_characteristic_polynomial] at hroot
  constructor
  · intro h
    have h0 := congrFun h 0
    norm_num at h0
  · ext i
    fin_cases i <;> simp [sourceHessian,base,point,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
    all_goals nlinarith

theorem actual_source_indefinite_directions :
    (![0,1] : Fin 2 → ℝ) ⬝ᵥ (sourceHessian base *ᵥ ![0,1])=1 ∧
    (![1,-1] : Fin 2 → ℝ) ⬝ᵥ (sourceHessian base *ᵥ ![1,-1])= -3 ∧
    ¬(sourceHessian base).PosSemidef ∧ ¬(-sourceHessian base).PosSemidef := by
  have hp : (![0,1] : Fin 2 → ℝ) ⬝ᵥ (sourceHessian base *ᵥ ![0,1])=1 := by
    norm_num [sourceHessian,base,point,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  have hn : (![1,-1] : Fin 2 → ℝ) ⬝ᵥ (sourceHessian base *ᵥ ![1,-1])= -3 := by
    norm_num [sourceHessian,base,point,Matrix.mulVec,dotProduct,Fin.sum_univ_two]
  refine ⟨hp,hn,?_,?_⟩
  · intro h
    have hb := h.dotProduct_mulVec_nonneg (![1,-1] : Fin 2 → ℝ)
    simp only [star_trivial,hn] at hb
    norm_num at hb
  · intro h
    have hb := h.dotProduct_mulVec_nonneg (![0,1] : Fin 2 → ℝ)
    simp only [star_trivial,Matrix.neg_mulVec,dotProduct_neg,hp] at hb
    norm_num at hb

theorem actual_source_eigenvalue_roundings :
    |(1+Real.sqrt 17)/2-(2.56:ℝ)|<0.005 ∧
    |(1-Real.sqrt 17)/2-(-1.56:ℝ)|<0.005 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤17)
  have hn := Real.sqrt_nonneg (17:ℝ)
  have hl : (4.123:ℝ)<Real.sqrt 17 := by nlinarith
  have hu : Real.sqrt 17<(4.124:ℝ) := by nlinarith
  constructor <;> apply abs_lt.mpr <;> constructor <;> linarith

theorem actual_remainder_identity (delta : E) :
    remainder delta=(delta 0)^2*delta 1+Real.exp (delta 1)-(1+delta 1+(delta 1)^2/2) := by
  simp [remainder,objective,secondModel,base,point]
  ring

theorem actual_remainder_norm_bound (delta : E) (hd : ‖delta‖≤1) :
    |remainder delta|≤(11/9:ℝ)*‖delta‖^3 := by
  have h0 : |delta 0|≤‖delta‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le delta 0
  have h1 : |delta 1|≤‖delta‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le delta 1
  have he := Real.exp_bound (x := delta 1) (h1.trans hd) (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ] at he
  have he' : |Real.exp (delta 1)-(1+delta 1+(delta 1)^2/2)|≤(2/9:ℝ)*|delta 1|^3 := by
    convert he using 1 <;> ring
  have hp : |(delta 0)^2*delta 1|≤‖delta‖^3 := by
    rw [abs_mul,abs_pow]
    calc
      |delta 0|^2*|delta 1|≤‖delta‖^2*‖delta‖ := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 2) h1 (abs_nonneg _) (sq_nonneg _)
      _=‖delta‖^3 := by ring
  have hx : |delta 1|^3≤‖delta‖^3 := pow_le_pow_left₀ (abs_nonneg _) h1 3
  rw [actual_remainder_identity]
  have hb := abs_add_le ((delta 0)^2*delta 1) (Real.exp (delta 1)-(1+delta 1+(delta 1)^2/2))
  have hr : (delta 0)^2*delta 1+Real.exp (delta 1)-(1+delta 1+(delta 1)^2/2)=
      (delta 0)^2*delta 1+(Real.exp (delta 1)-(1+delta 1+(delta 1)^2/2)) := by ring
  rw [hr]
  linarith

theorem actual_remainder_is_cubic_bigO :
    remainder=O[𝓝 (0:E)] (fun delta : E => ‖delta‖^3) := by
  apply Asymptotics.IsBigO.of_bound (11/9)
  filter_upwards [Metric.ball_mem_nhds (0:E) (by norm_num : (0:ℝ)<1)] with delta hd
  have hn : ‖delta‖≤1 := (by simpa only [Metric.mem_ball,dist_zero_right] using hd : ‖delta‖<1).le
  simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (norm_nonneg delta) 3)] using actual_remainder_norm_bound delta hn

theorem actual_source_predictions_and_true_value :
    firstModel (point (1/10) (1/10))=6/5 ∧
    secondModel (point (1/10) (1/10))=49/40 ∧
    objective (point (11/10) (1/10))=121/1000+Real.exp (1/10) ∧
    |objective (point (11/10) (1/10))-(1.226171:ℝ)|<0.0000005 ∧
    |remainder (point (1/10) (1/10))-(0.00117:ℝ)|<0.000005 ∧
    objective (point (11/10) (1/10))<(1.226171:ℝ) := by
  have he := abs_lt.mp CompleteFoundationsTaylorModels.actual_exp_tenth_decimal
  norm_num [firstModel,secondModel,objective,remainder,base,point]
  repeat' constructor
  all_goals try (apply abs_lt.mpr;constructor)
  all_goals linarith

theorem actual_halving_displacement_reduces_error_by_about_eight :
    0<remainder (point (1/20) (1/20)) ∧
    8<remainder (point (1/10) (1/10))/remainder (point (1/20) (1/20)) ∧
    remainder (point (1/10) (1/10))/remainder (point (1/20) (1/20))<(8.1:ℝ) := by
  have h1 := abs_lt.mp CompleteFoundationsTaylorModels.actual_exp_tenth_decimal
  have h2 := Real.exp_bound (x := (1/20:ℝ)) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ] at h2
  have hlo := (abs_le.mp h2).1
  have hup := (abs_le.mp h2).2
  have hp : 0<remainder (point (1/20) (1/20)) := by
    simp [actual_remainder_identity,point]
    linarith
  refine ⟨hp,(lt_div_iff₀ hp).mpr ?_,(div_lt_iff₀ hp).mpr ?_⟩
  all_goals simp only [actual_remainder_identity,point,Matrix.cons_val_zero,Matrix.cons_val_one]
  all_goals norm_num
  all_goals linarith

end SafeLearning.CompleteFoundationsTaylorCheck
