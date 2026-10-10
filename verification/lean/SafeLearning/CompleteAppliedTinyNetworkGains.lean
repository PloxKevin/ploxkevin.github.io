import SafeLearning.CompleteAppliedTinyNetwork

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace SafeLearning.CompleteAppliedTinyNetworkGains
open SafeLearning.CompleteAppliedTinyNetwork

def outputMatrix : Matrix (Fin 1) (Fin 2) ℝ := fun _=>secondWeight

theorem actual_source_first_layer_spectral_norm_is_sqrt_two : ‖firstWeight‖=Real.sqrt 2 := by
  have hg : firstWeightᵀ*firstWeight=(2:ℝ)•(1:Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j;fin_cases i <;> fin_cases j <;>
      norm_num [firstWeight,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self firstWeight
  rw [show firstWeightᴴ=firstWeightᵀ by simp, hg,norm_smul] at h
  norm_num at h
  have hs : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  nlinarith [norm_nonneg firstWeight,Real.sqrt_nonneg (2:ℝ)]

theorem actual_source_output_layer_spectral_norm_is_sqrt_five_and_product_sqrt_ten :
    ‖outputMatrix‖=Real.sqrt 5 ∧ ‖outputMatrix‖*‖firstWeight‖=Real.sqrt 10 := by
  have hg : outputMatrix*outputMatrixᵀ=(5:ℝ)•(1:Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j;fin_cases i;fin_cases j
    norm_num [outputMatrix,secondWeight,Matrix.mul_apply,Fin.sum_univ_two,Matrix.one_apply]
  have h := Matrix.l2_opNorm_conjTranspose_mul_self outputMatrixᵀ
  have ht : ‖outputMatrixᵀ‖=‖outputMatrix‖ := Matrix.l2_opNorm_conjTranspose outputMatrix
  rw [show outputMatrixᵀᴴ=outputMatrix by simp,hg,norm_smul,ht] at h
  norm_num at h
  have hs : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  have hn : ‖outputMatrix‖=Real.sqrt 5 := by nlinarith [norm_nonneg outputMatrix,Real.sqrt_nonneg (5:ℝ)]
  refine ⟨hn,?_⟩
  rw [hn,actual_source_first_layer_spectral_norm_is_sqrt_two,←Real.sqrt_mul (by norm_num : (0:ℝ)≤5)]
  norm_num

theorem actual_both_active_region_is_affine_with_literal_steepest_slope (x : E)
    (h1 : 0≤x 0+x 1-1) (h2 : 0≤x 0-x 1) :
    network x=-x 0+3*x 1-2 ∧ ‖point (-1) 3‖=Real.sqrt 10 := by
  constructor
  · rw [(actual_network_is_the_literal_two_two_one_ReLU_composition x).2,
      max_eq_left h1,max_eq_left h2]
    ring
  · have h := EuclideanSpace.real_norm_sq_eq (point (-1) 3)
    norm_num [point,Fin.sum_univ_two] at h
    change ‖point (-1) 3‖^2=10 at h
    nlinarith [norm_nonneg (point (-1) 3),Real.sq_sqrt (by norm_num : (0:ℝ)≤10),Real.sqrt_nonneg (10:ℝ)]

theorem actual_network_exact_global_Euclidean_gain_is_sqrt_ten :
    IsLeast {L:ℝ | 0≤L ∧ ∀x y:E,|network x-network y|≤L*‖x-y‖} (Real.sqrt 10) := by
  refine ⟨⟨Real.sqrt_nonneg _,actual_network_global_Euclidean_gain_is_at_most_sqrt_ten⟩,?_⟩
  intro L hL
  have h := hL.2 (point 4 0) (point 3 3)
  have hval : |network (point 4 0)-network (point 3 3)|=10 := by
    rw [(actual_network_is_the_literal_two_two_one_ReLU_composition (point 4 0)).2,
      (actual_network_is_the_literal_two_two_one_ReLU_composition (point 3 3)).2]
    norm_num [point]
  have hnorm : ‖point 4 0-point 3 3‖^2=10 := by
    rw [actual_input_displacement_is_the_ordinary_Euclidean_norm]
    norm_num [point]
  have hdist : ‖point 4 0-point 3 3‖=Real.sqrt 10 := by
    nlinarith [norm_nonneg (point 4 0-point 3 3),Real.sq_sqrt (by norm_num : (0:ℝ)≤10),Real.sqrt_nonneg (10:ℝ)]
  rw [hval,hdist] at h
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<10)]

theorem actual_global_pixel_and_true_boundary_display_roundings_and_nonequalities :
    |(1/Real.sqrt 10)-(316/1000:ℝ)|<1/2000 ∧
    |(1/(2*Real.sqrt 10))-(158/1000:ℝ)|<1/2000 ∧
    |(2*Real.sqrt 2)-(283/100:ℝ)|<1/200 ∧
    (316/1000:ℝ)<1/Real.sqrt 10 ∧
    (158/1000:ℝ)<1/(2*Real.sqrt 10) ∧ 2*Real.sqrt 2<(283/100:ℝ) := by
  have hs10 : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  have hn10 : 0<Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  have hl10 : (3162277/1000000:ℝ)<Real.sqrt 10 := by nlinarith
  have hu10 : Real.sqrt 10<(3162278/1000000:ℝ) := by nlinarith
  have hs2 : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
  have hn2 := Real.sqrt_nonneg (2:ℝ)
  have hl2 : (1414213/1000000:ℝ)<Real.sqrt 2 := by nlinarith
  have hu2 : Real.sqrt 2<(1414214/1000000:ℝ) := by nlinarith
  have hglobal : (316/1000:ℝ)<1/Real.sqrt 10 := by rw [lt_div_iff₀ hn10];nlinarith
  have hpixel : (158/1000:ℝ)<1/(2*Real.sqrt 10) := by rw [lt_div_iff₀ (by positivity : 0<2*Real.sqrt 10)];nlinarith
  have hub : 1/Real.sqrt 10<(316/1000:ℝ)+1/2000 := by rw [div_lt_iff₀ hn10];nlinarith
  have hpub : 1/(2*Real.sqrt 10)<(158/1000:ℝ)+1/2000 := by rw [div_lt_iff₀ (by positivity : 0<2*Real.sqrt 10)];nlinarith
  refine ⟨?_,?_,?_,hglobal,hpixel,?_⟩
  · rw [abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> linarith
  · rw [abs_lt];constructor <;> linarith
  · linarith

theorem actual_distance_certificate_gap_ratios_are_about_nine_and_three :
    (89/10:ℝ)<(2*Real.sqrt 2)*Real.sqrt 10 ∧
    (2*Real.sqrt 2)*Real.sqrt 10<9 ∧
    (3:ℝ)<Real.sqrt 10 ∧ Real.sqrt 10<16/5 := by
  have hs : (Real.sqrt 10)^2=10 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (10:ℝ)
  have hprod : ((2*Real.sqrt 2)*Real.sqrt 10)^2=80 := by
    rw [mul_pow,mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤2),hs]
    norm_num
  have hnon : 0≤(2*Real.sqrt 2)*Real.sqrt 10 := by positivity
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith

end SafeLearning.CompleteAppliedTinyNetworkGains
