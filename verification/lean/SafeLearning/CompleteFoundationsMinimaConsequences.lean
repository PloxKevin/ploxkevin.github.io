import SafeLearning.CompleteFoundationsMinimaModels
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompleteFoundationsMinimaConsequences
open SafeLearning.CompleteFoundationsMinimaModels Set Filter
open scoped Topology

theorem actual_exp_strict_positivity (x : ℝ) : 0<Real.exp (-x) := Real.exp_pos _

theorem actual_exp_halfline_infimum :
    sInf ((fun x : ℝ=>Real.exp (-x)) '' Ici 0)=0 := by
  apply actual_exp_infimum_and_no_minimum.1.csInf_eq
  exact ⟨1,⟨0,by norm_num,by norm_num⟩⟩

theorem actual_halfspace_cauchy_chain (u : E) (hu : u∈feasible) :
    (1/2:ℝ)≤(u 0+u 1)^2/2 ∧ (u 0+u 1)^2/2≤‖u‖^2 := by
  have hf : 1≤u 0+u 1 := hu
  rw [actual_norm_squared]
  constructor <;> nlinarith [sq_nonneg (u 0-u 1)]

theorem actual_source_halfspace_attains :
    point (1/2) (1/2)∈feasible ∧ ‖point (1/2) (1/2)‖^2=(1/2:ℝ) ∧
    IsMinOn (fun u : E=>‖u‖^2) feasible (point (1/2) (1/2)) := by
  have hm : point (1/2) (1/2)∈feasible := by norm_num [point,feasible,linearSum]
  have hv : ‖point (1/2) (1/2)‖^2=(1/2:ℝ) := by
    rw [actual_norm_squared];norm_num [point]
  refine ⟨hm,hv,?_⟩
  intro u hu
  change ‖point (1/2) (1/2)‖^2≤‖u‖^2
  rw [hv]
  exact (actual_halfspace_norm_unique_minimum u hu).1

theorem actual_linear_diagonal_escape :
    (∀ s : ℝ,linearSum (point s s)=2*s) ∧
    Tendsto (fun s : ℝ=>linearSum (point s s)) atTop atTop := by
  have he (s : ℝ) : linearSum (point s s)=2*s := by simp [linearSum,point];ring
  refine ⟨he,?_⟩
  simp_rw [he]
  exact tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2)

theorem actual_below_one_sublevel_closed_bounded (c : ℝ) (hc : c<1) :
    IsClosed (sublevel c) ∧ Bornology.IsBounded (sublevel c) :=
  ⟨(actual_sublevel_compact_iff c).mpr hc |>.isClosed,
    (actual_sublevel_compact_iff c).mpr hc |>.isBounded⟩

theorem actual_sublevel_function_limit_at_infinity :
    Tendsto (fun x : ℝ=>x^2/(1+x^2)) (cocompact ℝ) (𝓝 1) := by
  have h := actual_sublevel_function_limit.1.comp (tendsto_norm_cocompact_atTop (E:=ℝ))
  simpa [Function.comp_def,Real.norm_eq_abs,sq_abs] using h

end SafeLearning.CompleteFoundationsMinimaConsequences
