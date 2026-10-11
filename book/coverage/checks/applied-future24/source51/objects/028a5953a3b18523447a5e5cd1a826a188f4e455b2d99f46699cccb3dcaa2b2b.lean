import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRealTightFrameTransport
variable {T D S K : Type*} [Fintype T] [Fintype D] [DecidableEq D]
  [Fintype S] [Fintype K] [DecidableEq K]

theorem actual_equivalent_feature_coordinates_preserve_euclidean_norm
    (x : K → ℝ) (e : D ≃ K) :
    ‖(WithLp.toLp 2 (fun i => x (e i)) : EuclideanSpace ℝ D)‖=
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ K)‖ := by
  have h : ‖(WithLp.toLp 2 (fun i => x (e i)) : EuclideanSpace ℝ D)‖^2=
      ‖(WithLp.toLp 2 x : EuclideanSpace ℝ K)‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => x (e i)) : EuclideanSpace ℝ D),
    norm_nonneg (WithLp.toLp 2 x : EuclideanSpace ℝ K)]

theorem actual_reindexing_the_samples_and_features_preserves_the_uniform_gram
    (X : Matrix S K ℝ) (eT : T ≃ S) (eD : D ≃ K)
    (hGram : Xᵀ*X=((Fintype.card S:ℝ)/(Fintype.card K:ℝ)) • (1 : Matrix K K ℝ)) :
    (X.submatrix eT eD)ᵀ*X.submatrix eT eD=
      ((Fintype.card T:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ) := by
  rw [Matrix.transpose_submatrix,Matrix.submatrix_mul_equiv,hGram]
  rw [Fintype.card_congr eT,Fintype.card_congr eD]
  ext i j
  change ((Fintype.card S:ℝ)/(Fintype.card K:ℝ)) * (1 : Matrix K K ℝ) (eD i) (eD j)=
    ((Fintype.card S:ℝ)/(Fintype.card K:ℝ)) * (1 : Matrix D D ℝ) i j
  simp only [Matrix.one_apply,eD.injective.eq_iff]

theorem actual_unit_norm_tight_frames_transport_across_both_index_equivalences
    (X : Matrix S K ℝ) (eT : T ≃ S) (eD : D ≃ K)
    (hNorm : ∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ K)‖=1)
    (hGram : Xᵀ*X=((Fintype.card S:ℝ)/(Fintype.card K:ℝ)) • (1 : Matrix K K ℝ)) :
    ∃ Y : Matrix T D ℝ,
      (∀ t,‖(WithLp.toLp 2 (fun i => Y t i) : EuclideanSpace ℝ D)‖=1) ∧
      Yᵀ*Y=((Fintype.card T:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ) := by
  refine ⟨X.submatrix eT eD,?_,
    actual_reindexing_the_samples_and_features_preserves_the_uniform_gram X eT eD hGram⟩
  intro t
  change ‖(WithLp.toLp 2 (fun i => X (eT t) (eD i)) : EuclideanSpace ℝ D)‖=1
  rw [actual_equivalent_feature_coordinates_preserve_euclidean_norm,hNorm]

end SafeLearning.CompleteModulesRealTightFrameTransport
