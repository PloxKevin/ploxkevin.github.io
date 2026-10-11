import SafeLearning.CompleteFoundationsFunctionExamples

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace ENNReal

namespace SafeLearning.CompleteFoundationsL2Models

def unitMeasure : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
abbrev H := Lp ℝ 2 unitMeasure

theorem constant_mem_l2 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 unitMeasure := by
  apply MonotoneOn.memLp_isCompact isCompact_Icc
  intro x hx y hy hxy
  exact le_rfl

theorem linear_mem_l2 : MemLp (fun x : ℝ => x) 2 unitMeasure := by
  apply MonotoneOn.memLp_isCompact isCompact_Icc
  intro x hx y hy hxy
  exact hxy

def constantF : H := constant_mem_l2.toLp (fun _ : ℝ => (1 : ℝ))
def linearG : H := linear_mem_l2.toLp (fun x : ℝ => x)

theorem actual_l2_inner_is_interval_integral (f g : ℝ → ℝ)
    (hf : MemLp f 2 unitMeasure) (hg : MemLp g 2 unitMeasure) :
    inner ℝ (hf.toLp f) (hg.toLp g)=∫ x : ℝ in (0 : ℝ)..1,f x*g x := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : ℝ,inner ℝ ((hf.toLp f) x) ((hg.toLp g) x) ∂unitMeasure)=
        ∫ x : ℝ,f x*g x ∂unitMeasure := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hfx hgx
      rw [hfx,hgx]
      simp [RCLike.inner_apply,mul_comm]
    _=∫ x : ℝ in (0 : ℝ)..1,f x*g x := by
      change (∫ x : ℝ in Icc (0 : ℝ) 1,f x*g x)=_
      rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

theorem actual_source_inner_products :
    inner ℝ constantF linearG=1/2 ∧ inner ℝ constantF constantF=1 ∧ inner ℝ linearG linearG=1/3 := by
  constructor
  · rw [constantF,linearG,actual_l2_inner_is_interval_integral]
    norm_num
  constructor
  · rw [constantF,actual_l2_inner_is_interval_integral]
    norm_num
  · rw [linearG,actual_l2_inner_is_interval_integral]
    simpa only [← pow_two] using SafeLearning.CompleteFoundationsFunctionExamples.projection_integrals.2.2.1

theorem actual_source_squared_norms : ‖constantF‖^2=1 ∧ ‖linearG‖^2=1/3 := by
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq,
    actual_source_inner_products.2.1,actual_source_inner_products.2.2]
  exact ⟨rfl,rfl⟩

theorem actual_source_norms : ‖constantF‖=1 ∧ ‖linearG‖=1/Real.sqrt 3 := by
  constructor
  · nlinarith [actual_source_squared_norms.1,norm_nonneg constantF]
  · have hroot : (Real.sqrt (1/3 : ℝ))^2=1/3 := Real.sq_sqrt (by norm_num)
    have hnorm : ‖linearG‖=Real.sqrt (1/3 : ℝ) :=
      (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (actual_source_squared_norms.2.trans hroot.symm)
    rw [hnorm]
    exact SafeLearning.CompleteFoundationsFunctionExamples.projection_norms.2.1

theorem actual_projection_characterization (c : ℝ) :
    inner ℝ constantF (linearG-c • constantF)=1/2-c ∧
    (inner ℝ constantF (linearG-c • constantF)=0 ↔ c=1/2) := by
  have h : inner ℝ constantF (linearG-c • constantF)=1/2-c := by
    rw [inner_sub_right,real_inner_smul_right,actual_source_inner_products.1,actual_source_inner_products.2.1]
    ring
  exact ⟨h,by rw [h];constructor <;> intro hh <;> linarith⟩

def residual : H := linearG-(1/2 : ℝ) • constantF

theorem actual_residual_orthogonality_and_norm :
    inner ℝ constantF residual=0 ∧ ‖residual‖^2=1/12 ∧
    ‖linearG‖^2=‖(1/2 : ℝ) • constantF‖^2+‖residual‖^2 := by
  have hgF : inner ℝ linearG constantF=1/2 := by
    rw [real_inner_comm]
    exact actual_source_inner_products.1
  have hr : ‖residual‖^2=1/12 := by
    rw [← real_inner_self_eq_norm_sq,residual,inner_sub_left,inner_sub_right,inner_sub_right,
      real_inner_smul_left,real_inner_smul_left,real_inner_smul_right,real_inner_smul_right,
      actual_source_inner_products.1,actual_source_inner_products.2.1,actual_source_inner_products.2.2,hgF]
    norm_num
  refine ⟨?_,hr,?_⟩
  · exact (actual_projection_characterization (1/2)).2.mpr rfl
  · rw [norm_smul,Real.norm_eq_abs,hr,mul_pow,actual_source_squared_norms.1,actual_source_squared_norms.2]
    norm_num

theorem actual_classes_have_source_representatives :
    (constantF : ℝ → ℝ)=ᵐ[unitMeasure] (fun _ : ℝ => (1 : ℝ)) ∧
    (linearG : ℝ → ℝ)=ᵐ[unitMeasure] (fun x : ℝ => x) :=
  ⟨constant_mem_l2.coeFn_toLp,linear_mem_l2.coeFn_toLp⟩

end SafeLearning.CompleteFoundationsL2Models
