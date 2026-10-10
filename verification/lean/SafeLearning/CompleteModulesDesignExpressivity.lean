import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology NNReal
namespace SafeLearning.CompleteModulesDesignExpressivity

def sourceGradient : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![2/5,1/500]
def sourceTarget (z : EuclideanSpace ℝ (Fin 2)) : ℝ := inner ℝ sourceGradient z

theorem actual_source_normalization_and_affine_gradient_formula
    (z : EuclideanSpace ℝ (Fin 2)) :
    (1/25:ℝ)*(10*z 0)+(1/50)*((1/10)*z 1)=sourceTarget z ∧
      sourceTarget z=(2/5)*z 0+(1/500)*z 1 ∧
      HasFDerivAt sourceTarget (innerSL ℝ sourceGradient) z := by
  have he : sourceTarget z=(2/5)*z 0+(1/500)*z 1 := by
    simp [sourceTarget,sourceGradient,PiLp.inner_apply,RCLike.inner_apply,
      Fin.sum_univ_two,mul_comm]
  refine ⟨by rw [he];ring,he,?_⟩
  exact (innerSL ℝ sourceGradient).hasFDerivAt

theorem actual_source_gradient_norm_and_printed_rounding :
    ‖sourceGradient‖^2=40001/250000 ∧
      ‖sourceGradient‖=Real.sqrt (40001/250000) ∧
      (3/10:ℝ)<‖sourceGradient‖ ∧
      |‖sourceGradient‖-(400005/1000000:ℝ)|<1/2000000 := by
  have hn : ‖sourceGradient‖^2=40001/250000 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [sourceGradient,Fin.sum_univ_two]
  have hroot : ‖sourceGradient‖=Real.sqrt (40001/250000) := by
    rw [←hn,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨hn,hroot,?_,?_⟩
  · nlinarith [norm_nonneg sourceGradient]
  · rw [abs_lt]
    constructor <;>nlinarith [norm_nonneg sourceGradient]

theorem actual_source_gradient_direction_attains_the_slope
    (z : EuclideanSpace ℝ (Fin 2)) (t : ℝ) (ht : 0<t) :
    |sourceTarget (z+t • sourceGradient)-sourceTarget z|=
      ‖sourceGradient‖*‖(z+t • sourceGradient)-z‖ := by
  have he : sourceTarget (z+t • sourceGradient)-sourceTarget z=
      t*‖sourceGradient‖^2 := by
    simp [sourceTarget,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq]
  rw [he,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht,
    abs_of_nonneg (mul_nonneg ht.le (sq_nonneg _))]
  ring

theorem actual_no_exact_matching_map_on_a_nonempty_open_region_has_budget_point_three
    (D : Set (EuclideanSpace ℝ (Fin 2))) (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hopen : IsOpen D) (hne : D.Nonempty)
    (hmatch : ∀ z∈D,f z=sourceTarget z) :
    ¬LipschitzOnWith (3/10:ℝ≥0) f D := by
  intro hbudget
  obtain ⟨z,hz⟩:=hne
  have hdmem : ∀ᶠ x in 𝓝 z,x∈D := hopen.mem_nhds hz
  have heq : f =ᶠ[𝓝 z] sourceTarget :=
    hdmem.mono (fun x hx=>hmatch x hx)
  have hd : HasFDerivAt f (innerSL ℝ sourceGradient) z :=
    (actual_source_normalization_and_affine_gradient_formula z).2.2.congr_of_eventuallyEq heq
  have hb:=norm_fderiv_le_of_lipschitzOn ℝ (hopen.mem_nhds hz) hbudget
  rw [hd.fderiv,innerSL_apply_norm] at hb
  norm_num only [NNReal.coe_div,NNReal.coe_ofNat] at hb
  exact (not_le_of_gt actual_source_gradient_norm_and_printed_rounding.2.2.1) hb

end SafeLearning.CompleteModulesDesignExpressivity
