import SafeLearning.CompleteModulesGaussianTailNumericalBounds
import SafeLearning.CompleteModulesLandscapeARStableMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
noncomputable section
open Set
open scoped BigOperators
namespace SafeLearning.CompleteModulesLandscapeARTailTable
open CompleteAppliedGaussianCDF CompleteAppliedGaussianTailIntegral
open CompleteModulesGaussianTailNumericalBounds CompleteModulesLandscapeARGaussianAlgebra
open CompleteModulesLandscapeARStableMoments

def polyQ (r : ℚ) : ℚ := ∑i∈Finset.range 50,(-1/2:ℚ)^i*r^(2*i+1)/((i.factorial:ℚ)*(2*i+1))
def numeratorQ (t : ℕ) : ℚ := 1-(4/5)*(1-(1/2)^t)
def varianceQ (t : ℕ) : ℚ := (1/75)*(1-(1/4)^t)
def literalTail (t : ℕ) : ℝ := 1-standardCDF ((numeratorQ t:ℝ)/Real.sqrt (varianceQ t:ℝ))
def radiusLower (t : Fin 39) : ℚ :=
  match t.val with
  | 0 => (35777/10000:ℚ)
  | 1 => (261861/100000:ℚ)
  | 2 => (21693/10000:ℚ)
  | 3 => (3899/2000:ℚ)
  | 4 => (46013/25000:ℚ)
  | 5 => (178623/100000:ℚ)
  | 6 => (21989/12500:ℚ)
  | 7 => (87279/50000:ℚ)
  | 8 => (173881/100000:ℚ)
  | 9 => (173543/100000:ℚ)
  | 10 => (86687/50000:ℚ)
  | 11 => (173289/100000:ℚ)
  | 12 => (173247/100000:ℚ)
  | 13 => (86613/50000:ℚ)
  | 14 => (34643/20000:ℚ)
  | 15 => (17321/10000:ℚ)
  | 16 => (173207/100000:ℚ)
  | 17 => (86603/50000:ℚ)
  | 18 => (34641/20000:ℚ)
  | 19 => (34641/20000:ℚ)
  | 20 => (34641/20000:ℚ)
  | 21 => (34641/20000:ℚ)
  | 22 => (34641/20000:ℚ)
  | 23 => (34641/20000:ℚ)
  | 24 => (34641/20000:ℚ)
  | 25 => (34641/20000:ℚ)
  | 26 => (34641/20000:ℚ)
  | 27 => (34641/20000:ℚ)
  | 28 => (34641/20000:ℚ)
  | 29 => (34641/20000:ℚ)
  | 30 => (34641/20000:ℚ)
  | 31 => (34641/20000:ℚ)
  | 32 => (34641/20000:ℚ)
  | 33 => (34641/20000:ℚ)
  | 34 => (34641/20000:ℚ)
  | 35 => (34641/20000:ℚ)
  | 36 => (34641/20000:ℚ)
  | 37 => (34641/20000:ℚ)
  | _ => (34641/20000:ℚ)
def radiusUpper (t : Fin 39) : ℚ :=
  match t.val with
  | 0 => (357771/100000:ℚ)
  | 1 => (130931/50000:ℚ)
  | 2 => (216931/100000:ℚ)
  | 3 => (194951/100000:ℚ)
  | 4 => (184053/100000:ℚ)
  | 5 => (5582/3125:ℚ)
  | 6 => (175913/100000:ℚ)
  | 7 => (174559/100000:ℚ)
  | 8 => (86941/50000:ℚ)
  | 9 => (21693/12500:ℚ)
  | 10 => (1387/800:ℚ)
  | 11 => (17329/10000:ℚ)
  | 12 => (5414/3125:ℚ)
  | 13 => (173227/100000:ℚ)
  | 14 => (5413/3125:ℚ)
  | 15 => (173211/100000:ℚ)
  | 16 => (21651/12500:ℚ)
  | 17 => (173207/100000:ℚ)
  | 18 => (86603/50000:ℚ)
  | 19 => (86603/50000:ℚ)
  | 20 => (86603/50000:ℚ)
  | 21 => (86603/50000:ℚ)
  | 22 => (86603/50000:ℚ)
  | 23 => (86603/50000:ℚ)
  | 24 => (86603/50000:ℚ)
  | 25 => (86603/50000:ℚ)
  | 26 => (86603/50000:ℚ)
  | 27 => (86603/50000:ℚ)
  | 28 => (86603/50000:ℚ)
  | 29 => (86603/50000:ℚ)
  | 30 => (86603/50000:ℚ)
  | 31 => (86603/50000:ℚ)
  | 32 => (86603/50000:ℚ)
  | 33 => (86603/50000:ℚ)
  | 34 => (86603/50000:ℚ)
  | 35 => (86603/50000:ℚ)
  | 36 => (86603/50000:ℚ)
  | 37 => (86603/50000:ℚ)
  | _ => (86603/50000:ℚ)
def probLower (t : Fin 39) : ℚ :=
  match t.val with
  | 0 => (43/250000:ℚ)
  | 1 => (4413/1000000:ℚ)
  | 2 => (3757/250000:ℚ)
  | 3 => (1601/62500:ℚ)
  | 4 => (8211/250000:ℚ)
  | 5 => (37029/1000000:ℚ)
  | 6 => (9819/250000:ℚ)
  | 7 => (40439/1000000:ℚ)
  | 8 => (5129/125000:ℚ)
  | 9 => (4133/100000:ℚ)
  | 10 => (1037/25000:ℚ)
  | 11 => (8311/200000:ℚ)
  | 12 => (5199/125000:ℚ)
  | 13 => (41611/1000000:ℚ)
  | 14 => (41621/1000000:ℚ)
  | 15 => (333/8000:ℚ)
  | 16 => (10407/250000:ℚ)
  | 17 => (41629/1000000:ℚ)
  | 18 => (4163/100000:ℚ)
  | 19 => (4163/100000:ℚ)
  | 20 => (4163/100000:ℚ)
  | 21 => (4163/100000:ℚ)
  | 22 => (4163/100000:ℚ)
  | 23 => (4163/100000:ℚ)
  | 24 => (4163/100000:ℚ)
  | 25 => (4163/100000:ℚ)
  | 26 => (4163/100000:ℚ)
  | 27 => (4163/100000:ℚ)
  | 28 => (4163/100000:ℚ)
  | 29 => (4163/100000:ℚ)
  | 30 => (4163/100000:ℚ)
  | 31 => (4163/100000:ℚ)
  | 32 => (4163/100000:ℚ)
  | 33 => (4163/100000:ℚ)
  | 34 => (4163/100000:ℚ)
  | 35 => (4163/100000:ℚ)
  | 36 => (4163/100000:ℚ)
  | 37 => (4163/100000:ℚ)
  | _ => (4163/100000:ℚ)
def probUpper (t : Fin 39) : ℚ :=
  match t.val with
  | 0 => (7/40000:ℚ)
  | 1 => (69/15625:ℚ)
  | 2 => (1879/125000:ℚ)
  | 3 => (25619/1000000:ℚ)
  | 4 => (2053/62500:ℚ)
  | 5 => (37033/1000000:ℚ)
  | 6 => (491/12500:ℚ)
  | 7 => (10111/250000:ℚ)
  | 8 => (10259/250000:ℚ)
  | 9 => (20667/500000:ℚ)
  | 10 => (10371/250000:ℚ)
  | 11 => (41559/1000000:ℚ)
  | 12 => (41597/1000000:ℚ)
  | 13 => (8323/200000:ℚ)
  | 14 => (333/8000:ℚ)
  | 15 => (41629/1000000:ℚ)
  | 16 => (1301/31250:ℚ)
  | 17 => (41633/1000000:ℚ)
  | 18 => (20817/500000:ℚ)
  | 19 => (20817/500000:ℚ)
  | 20 => (20817/500000:ℚ)
  | 21 => (20817/500000:ℚ)
  | 22 => (20817/500000:ℚ)
  | 23 => (20817/500000:ℚ)
  | 24 => (20817/500000:ℚ)
  | 25 => (20817/500000:ℚ)
  | 26 => (20817/500000:ℚ)
  | 27 => (20817/500000:ℚ)
  | 28 => (20817/500000:ℚ)
  | 29 => (20817/500000:ℚ)
  | 30 => (20817/500000:ℚ)
  | 31 => (20817/500000:ℚ)
  | 32 => (20817/500000:ℚ)
  | 33 => (20817/500000:ℚ)
  | 34 => (20817/500000:ℚ)
  | 35 => (20817/500000:ℚ)
  | 36 => (20817/500000:ℚ)
  | 37 => (20817/500000:ℚ)
  | _ => (20817/500000:ℚ)

theorem actual_rational_polynomial_is_the_true_real_polynomial (r : ℚ) :
    (polyQ r:ℝ) = actualTailPolynomialIntegral (r:ℝ) := by
  unfold polyQ actualTailPolynomialIntegral
  push_cast
  rfl

theorem actual_literal_parameters_have_the_true_derived_rational_mean_and_variance (t : ℕ) :
    1-trueMean (1/2) (4/5) t = (numeratorQ t:ℝ) ∧
    trueVariance (1/2) (1/10) t = (varianceQ t:ℝ) := by
  constructor
  · simp only [trueMean, numeratorQ]
    push_cast
    norm_num only [show (1-(1/2:ℝ))=(1/2:ℝ) by norm_num]
  · rw [actual_true_variance_has_the_printed_closed_geometric_formula (1/2) (1/10) (by norm_num) (by norm_num)]
    simp only [varianceQ]
    push_cast
    rw [show (1-(1/2:ℝ))^(2*t)=(1/4:ℝ)^t by rw [pow_mul];norm_num]
    ring

theorem actual_all_thirty_nine_rational_rows_are_verified_by_trusted_kernel_decision :
    ∀ t : Fin 39,
      0 < numeratorQ (t.val+2) ∧ 0 < varianceQ (t.val+2) ∧
      0 < radiusLower t ∧ radiusLower t < radiusUpper t ∧ radiusUpper t < 4 ∧
      (radiusLower t)^2*varianceQ (t.val+2) < (numeratorQ (t.val+2))^2 ∧
      (numeratorQ (t.val+2))^2 < (radiusUpper t)^2*varianceQ (t.val+2) ∧
      0 ≤ polyQ (radiusLower t)-1/2500000000000000 ∧
      0 ≤ polyQ (radiusUpper t)-1/2500000000000000 ∧ polyQ (radiusLower t) < 2 ∧
      probLower t < 1/2-(3989424/10000000)*(polyQ (radiusUpper t)+1/2500000000000000) ∧
      1/2-(3989422/10000000)*(polyQ (radiusLower t)-1/2500000000000000) < probUpper t := by
  decide +kernel

theorem actual_each_transient_gaussian_tail_has_the_verified_rational_interval (t : Fin 39) :
    (probLower t:ℝ) < literalTail (t.val+2) ∧ literalTail (t.val+2) < (probUpper t:ℝ) := by
  obtain ⟨hn,hv,hl,hlU,hu,hlsq,husq,hpl,hpu,hpbound,hplow,hpup⟩ :=
    actual_all_thirty_nine_rational_rows_are_verified_by_trusted_kernel_decision t
  have hrad : (radiusLower t:ℝ) < (numeratorQ (t.val+2):ℝ)/Real.sqrt (varianceQ (t.val+2):ℝ) ∧
      (numeratorQ (t.val+2):ℝ)/Real.sqrt (varianceQ (t.val+2):ℝ) < (radiusUpper t:ℝ) := by
    apply actual_positive_denominator_squared_bounds_give_true_standardized_bounds
    · exact_mod_cast hn
    · exact_mod_cast hv
    · exact_mod_cast hl.le
    · exact_mod_cast hl.trans hlU
    · exact_mod_cast hlsq
    · exact_mod_cast husq
  have hpL : (probLower t:ℝ) < 1-standardCDF (radiusUpper t:ℝ) := by
    apply (actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
      (radiusUpper t:ℝ) (probLower t:ℝ) (1:ℝ) ?_ ?_ ?_ ?_).1
    · constructor
      · exact_mod_cast (hl.trans hlU).le
      · exact_mod_cast hu.le
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have he := (Rat.cast_le (K := ℝ)).mpr hpu
      push_cast at he
      norm_num only at he ⊢
      exact he
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have he := (Rat.cast_lt (K := ℝ)).mpr hplow
      push_cast at he
      norm_num only at he ⊢
      exact he
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have hc : 1/2-(3989422/10000000:ℚ)*(polyQ (radiusUpper t)-1/2500000000000000) < 1 := by nlinarith
      have he := (Rat.cast_lt (K := ℝ)).mpr hc
      push_cast at he
      norm_num only at he ⊢
      exact he
  have hpU : 1-standardCDF (radiusLower t:ℝ) < (probUpper t:ℝ) := by
    apply (actual_rational_polynomial_bounds_control_the_true_gaussian_upper_tail
      (radiusLower t:ℝ) (-1:ℝ) (probUpper t:ℝ) ?_ ?_ ?_ ?_).2
    · exact ⟨by exact_mod_cast hl.le, by
        exact_mod_cast (hlU.trans hu).le⟩
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have he := (Rat.cast_le (K := ℝ)).mpr hpl
      push_cast at he
      norm_num only at he ⊢
      exact he
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have hc : (-1:ℚ) < 1/2-(3989424/10000000)*(polyQ (radiusLower t)+1/2500000000000000) := by
        -- Both polynomial evaluations are below the Gaussian integral's coarse bound 4.
        nlinarith
      have he := (Rat.cast_lt (K := ℝ)).mpr hc
      push_cast at he
      norm_num only at he ⊢
      exact he
    · rw [←actual_rational_polynomial_is_the_true_real_polynomial]
      have he := (Rat.cast_lt (K := ℝ)).mpr hpup
      push_cast at he
      norm_num only at he ⊢
      exact he
  exact actual_standardized_tail_inherits_both_true_endpoint_probability_bounds
    _ _ _ _ _ ⟨hrad.1.le,hrad.2.le⟩ hpL hpU

end SafeLearning.CompleteModulesLandscapeARTailTable
