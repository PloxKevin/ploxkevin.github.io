import SafeLearning.CompletePolicyQuadraticDual

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Set Matrix
open scoped Matrix Topology
namespace SafeLearning.CompletePolicyQuadraticCalculus
open SafeLearning.CompletePolicyQuadraticDual
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def dotCLM (v : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj i

theorem actual_linear_form_apply (v x : ι → ℝ) : dotCLM v x = v ⬝ᵥ x := by
  simp [dotCLM, dotProduct]

theorem actual_linear_form_derivative (v x : ι → ℝ) :
    HasFDerivAt (fun y => v ⬝ᵥ y) (dotCLM v) x := by
  simpa only [actual_linear_form_apply] using (dotCLM v).hasFDerivAt

theorem actual_metric_quadratic_derivative (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (x : ι → ℝ) :
    HasFDerivAt (fun y => y ⬝ᵥ (H *ᵥ y)) (dotCLM (2 • (H *ᵥ x))) x := by
  have hd := HasFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (hasFDerivAt_apply i x).mul (actual_linear_form_derivative (H i) x))
  convert hd using 1
  · funext y
    rfl
  · ext d
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      actual_linear_form_apply, Finset.sum_add_distrib]
    change (2 • (H *ᵥ x)) ⬝ᵥ d = x ⬝ᵥ (H *ᵥ d) + d ⬝ᵥ (H *ᵥ x)
    rw [actual_real_symmetric_form H hH x d, smul_dotProduct, dotProduct_comm (H *ᵥ x) d]
    simp only [smul_eq_mul]
    ring

theorem actual_lagrangian_frechet_gradient (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam nu : ℝ) (x : ι → ℝ) :
    HasFDerivAt (lagrangian H g b c δ lam nu)
      (dotCLM (g - nu • b - lam • (H *ᵥ x))) x := by
  have hq := (actual_metric_quadratic_derivative H hH x).mul_const (1 / 2 : ℝ)
  have hcost := ((actual_linear_form_derivative b x).const_add c).const_mul nu
  have htrust := (hq.sub_const δ).const_mul lam
  have hd := ((actual_linear_form_derivative g x).sub hcost).sub htrust
  convert hd using 1
  · funext y
    simp [lagrangian,div_eq_mul_inv]
  · ext d
    simp [actual_linear_form_apply, sub_dotProduct, smul_dotProduct]
    ring

theorem actual_lagrangian_is_strictly_concave (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam nu : ℝ) (hlam : 0 < lam) :
    StrictConcaveOn ℝ univ (lagrangian H g b c δ lam nu) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ hxy a z ha hz hsum
  have hp : 0 < (x-y) ⬝ᵥ (H *ᵥ (x-y)) := by
    simpa using hH.dotProduct_mulVec_pos (sub_ne_zero.mpr hxy)
  have he : lagrangian H g b c δ lam nu (a • x + z • y) -
      (a * lagrangian H g b c δ lam nu x + z * lagrangian H g b c δ lam nu y) =
      (lam/2)*a*z*((x-y) ⬝ᵥ (H *ᵥ (x-y))) := by
    have hz : z = 1-a := by linarith
    simp only [lagrangian,mulVec_add,mulVec_smul,mulVec_sub,dotProduct_add,
      add_dotProduct,smul_dotProduct,dotProduct_smul,dotProduct_sub,sub_dotProduct,
      smul_eq_mul]
    rw [actual_real_symmetric_form H hH y x, hz]
    ring
  have hpos : 0 < (lam/2)*a*z*((x-y) ⬝ᵥ (H *ᵥ (x-y))) := by positivity
  simp only [smul_eq_mul]
  linarith

theorem actual_q_r_s_expansion (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (nu : ℝ) :
    (g-nu • b) ⬝ᵥ (H⁻¹ *ᵥ (g-nu • b)) =
      g ⬝ᵥ (H⁻¹ *ᵥ g) - 2*nu*(g ⬝ᵥ (H⁻¹ *ᵥ b)) + nu^2*(b ⬝ᵥ (H⁻¹ *ᵥ b)) := by
  simp only [mulVec_sub,mulVec_smul,dotProduct_sub,sub_dotProduct,smul_dotProduct,
    dotProduct_smul,smul_eq_mul]
  rw [actual_real_symmetric_form H⁻¹ hH.inv b g]
  ring

theorem actual_dual_lambda_partial (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam nu : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t => actualDual H g b c δ (t,nu))
      (-((g-nu • b) ⬝ᵥ (H⁻¹ *ᵥ (g-nu • b))) / (2*lam^2)+δ) lam := by
  have hd := (((hasDerivAt_const lam ((g-nu • b) ⬝ᵥ (H⁻¹ *ᵥ (g-nu • b)))).div
    ((hasDerivAt_id lam).const_mul 2) (by positivity : (2 : ℝ)*lam ≠ 0)).sub_const (nu*c)).add
      ((hasDerivAt_id lam).mul_const δ)
  have hc : HasDerivAt (fun t => closedDual H g b c δ t nu)
      (-((g-nu • b) ⬝ᵥ (H⁻¹ *ᵥ (g-nu • b))) / (2*lam^2)+δ) lam := by
    convert hd using 1 <;> simp [closedDual]
    field_simp [ne_of_gt hlam]
    <;> ring
  apply hc.congr_of_eventuallyEq
  exact (eventually_gt_nhds hlam).mono (fun t ht => actual_true_supremum_equals_closed_dual H hH g b c δ t nu ht)

theorem actual_dual_nu_partial (H : Matrix ι ι ℝ) (hH : H.PosDef)
    (g b : ι → ℝ) (c δ lam nu : ℝ) (hlam : 0 < lam) :
    HasDerivAt (fun t => actualDual H g b c δ (lam,t))
      ((nu*(b ⬝ᵥ (H⁻¹ *ᵥ b))-(g ⬝ᵥ (H⁻¹ *ᵥ b)))/lam-c) nu := by
  have hd := (((hasDerivAt_const nu (g ⬝ᵥ (H⁻¹ *ᵥ g))).sub
    ((hasDerivAt_id nu).const_mul (2*(g ⬝ᵥ (H⁻¹ *ᵥ b))))).add
    (((hasDerivAt_id nu).pow 2).mul_const (b ⬝ᵥ (H⁻¹ *ᵥ b)))).div_const (2*lam)
  have hp := (hd.sub ((hasDerivAt_id nu).mul_const c)).add_const (lam*δ)
  have he : (fun t => actualDual H g b c δ (lam,t)) =
      (fun t => (g ⬝ᵥ (H⁻¹ *ᵥ g)-2*t*(g ⬝ᵥ (H⁻¹ *ᵥ b))+t^2*(b ⬝ᵥ (H⁻¹ *ᵥ b)))/(2*lam)-t*c+lam*δ) := by
    funext t
    rw [actual_true_supremum_equals_closed_dual H hH g b c δ lam t hlam,
      closedDual,actual_q_r_s_expansion H hH g b t]
  rw [he]
  convert hp using 1
  simp
  field_simp [ne_of_gt hlam]
  <;> ring

end SafeLearning.CompletePolicyQuadraticCalculus
