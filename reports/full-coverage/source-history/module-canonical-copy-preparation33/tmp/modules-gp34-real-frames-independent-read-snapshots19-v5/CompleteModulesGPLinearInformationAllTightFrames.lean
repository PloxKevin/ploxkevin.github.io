import SafeLearning.CompleteModulesRealUnitNormTightFrameExistence
import SafeLearning.CompleteModulesGPLinearInformationMaxima
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix Set
namespace SafeLearning.CompleteModulesGPLinearInformationAllTightFrames
open CompleteModulesRealUnitNormTightFrameExistence CompleteModulesGPLinearInformationMaxima
variable {T D : Type*} [Fintype T] [Fintype D] [DecidableEq T] [DecidableEq D]

theorem actual_every_positive_dimension_at_most_the_sample_count_has_a_maximizing_design
    [Nonempty D] (hOrder : Fintype.card D≤Fintype.card T)
    (lambda : ℝ) (hlambda : 0<lambda) :
    IsGreatest (admissibleInformationValues T D lambda)
      ((Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ)))) := by
  obtain ⟨X,hNorm,hGram⟩ :=
    actual_real_unit_norm_tight_frames_exist_for_every_positive_dimension_below_the_sample_count hOrder
  exact actual_any_true_unit_norm_tight_frame_attains_the_dimension_bound
    X lambda hlambda hNorm hGram

theorem actual_large_sample_maximum_is_the_supremum_over_the_whole_unit_ball_design_set
    [Nonempty D] (hOrder : Fintype.card D≤Fintype.card T)
    (lambda : ℝ) (hlambda : 0<lambda) :
    sSup (admissibleInformationValues T D lambda)=
      ((Fintype.card D:ℝ)/2*Real.log
        (1+(Fintype.card T:ℝ)/(lambda*(Fintype.card D:ℝ)))) :=
  (actual_every_positive_dimension_at_most_the_sample_count_has_a_maximizing_design
    hOrder lambda hlambda).csSup_eq

end SafeLearning.CompleteModulesGPLinearInformationAllTightFrames
