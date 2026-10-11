import SafeLearning.CompletePolicyCDTTokens
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace SafeLearning.CompletePolicyCDTDomain
open Set
open SafeLearning.CompletePolicyCDTTokens

def identicalOnTrainingSafe (budget : ℝ) : ℝ := 0
def identicalOnTrainingUnsafe (budget : ℝ) : ℝ := if budget<0 then 1 else 0

theorem actual_training_domain_does_not_determine_negative_budget_behavior :
    (∀ budget : ℝ,0≤budget→identicalOnTrainingSafe budget=identicalOnTrainingUnsafe budget) ∧
    identicalOnTrainingSafe (-1)≠identicalOnTrainingUnsafe (-1) := by
  constructor
  · intro budget hb
    simp [identicalOnTrainingSafe,identicalOnTrainingUnsafe,not_lt.mpr hb]
  · norm_num [identicalOnTrainingSafe,identicalOnTrainingUnsafe]

theorem actual_all_relabel_training_costs_cannot_distinguish_models
    (target : ℝ) (horizon time : ℕ) (cost : ℕ→ℝ)
    (hc : ∀ step,0≤cost step) (ht : episodeTotal horizon cost≤target) :
    identicalOnTrainingSafe (shiftedToken target horizon time cost)=
      identicalOnTrainingUnsafe (shiftedToken target horizon time cost) := by
  exact actual_training_domain_does_not_determine_negative_budget_behavior.1 _
    (actual_nonnegative_training_cost_tokens target horizon time cost hc ht)

def unconditionalUnsafeChoice (rewardToken costToken : ℝ) : Fin 5 := 0

theorem actual_conditioning_tokens_alone_do_not_force_cost_priority :
    datasetCost (unconditionalUnsafeChoice 6 10)>10 ∧
    datasetReward (unconditionalUnsafeChoice 6 10)=10 := by
  norm_num [unconditionalUnsafeChoice,datasetCost,datasetReward]

end SafeLearning.CompletePolicyCDTDomain
