import SafeLearning.CompleteFoundationsNormDuality
import SafeLearning.CompleteFoundationsCenteredCubeNetsWhole30
import SafeLearning.CompleteFoundationsQuadraticTwentyNet24
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators NNReal
namespace SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32
open CompleteFoundationsNormDuality
open CompleteFoundationsCenteredCubeNetsWhole30
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball
    (s : ℝ) (hs : 0 ≤ s) (c x : EuclideanSpace ℝ I)
    (hx : ∀ i,|x i-c i| ≤ s/2) :
    dist x c ≤ s*Real.sqrt (Fintype.card I)/2 := by
  have hInf : ‖(fun i => x i-c i : I → ℝ)‖ ≤ s/2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ s/2)).mpr
    intro i
    simpa only [Real.norm_eq_abs] using hx i
  calc
    dist x c=l2Norm (fun i => x i-c i) := by
      rw [dist_eq_norm]
      congr 1
    _ ≤ Real.sqrt (Fintype.card I)*(s/2) :=
      actual_infinity_ball_in_euclidean_ball _ _ (by positivity) hInf
    _=s*Real.sqrt (Fintype.card I)/2 := by ring

theorem actual_cube_corner_attains_the_half_diagonal_radius
    (s : ℝ) (hs : 0 ≤ s) (c : EuclideanSpace ℝ I) :
    dist (c+WithLp.toLp 2 (fun _ : I => s/2)) c=s*Real.sqrt (Fintype.card I)/2 := by
  calc
    _=l2Norm (fun _ : I => s/2) := by
      rw [dist_eq_norm,add_sub_cancel_left]
      rfl
    _=Real.sqrt (Fintype.card I)*(s/2) :=
      actual_constant_vector_attains_dimension_conversion _ (by positivity)
    _=s*Real.sqrt (Fintype.card I)/2 := by ring

theorem actual_isometric_cube_image_has_the_same_half_diagonal_ball
    (s : ℝ) (hs : 0 ≤ s) (c x : EuclideanSpace ℝ I)
    (hx : ∀ i,|x i-c i| ≤ s/2)
    (e : EuclideanSpace ℝ I → EuclideanSpace ℝ I) (he : Isometry e) :
    dist (e x) (e c) ≤ s*Real.sqrt (Fintype.card I)/2 := by
  rw [he.dist_eq]
  exact actual_arbitrary_side_centered_cube_lies_in_its_half_diagonal_Euclidean_ball s hs c x hx

theorem actual_general_finite_net_transfers_every_sampled_lower_margin
    {E : Type*} [PseudoMetricSpace E] (D : Set E) (Z : Finset E)
    (L : ℝ≥0) (tau m0 : ℝ) (f : E → ℝ)
    (hf : LipschitzOnWith L f D) (hnet : IsFiniteNet D Z tau)
    (hm : ∀ z∈Z,m0 ≤ f z) :
    ∀ x∈D,m0-(L:ℝ)*tau ≤ f x := by
  exact CompleteFoundationsQuadraticTwentyNet24.actual_net_margin_certificate
    f D L tau m0 hf (Z : Set E) hnet.1 hnet.2 hm

theorem actual_printed_ceiling_grid_cardinality_coverage_and_full_margin_compose
    (d : ℕ) (hd : 0 < d) (tau : ℝ) (ht : 0 < tau) :
    let N:=Nat.ceil (Real.sqrt d/(2*tau))
    IsFiniteNet (unitCube d) (centeredGrid d N) tau ∧
      (centeredGrid d N).card=N^d ∧
      ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ≥0) (m0 : ℝ),
        LipschitzOnWith L f (unitCube d) →
        (∀ z∈centeredGrid d N,m0 ≤ f z) →
        ∀ x∈unitCube d,m0-(L:ℝ)*tau ≤ f x := by
  dsimp only
  have hN:=actual_ceiling_grid_radius d hd tau ht
  have hGrid:=actual_centered_grid_covers d _ hN.1
  have hnet : IsFiniteNet (unitCube d)
      (centeredGrid d (Nat.ceil (Real.sqrt d/(2*tau)))) tau := by
    refine ⟨hGrid.1,?_⟩
    intro x hx
    obtain ⟨z,hz,he⟩:=hGrid.2 x hx
    exact ⟨z,hz,he.trans hN.2⟩
  refine ⟨hnet,actual_centered_grid_cardinality d _ hN.1,?_⟩
  intro f L m0 hf hm
  exact actual_general_finite_net_transfers_every_sampled_lower_margin _ _ _ _ _ _ hf hnet hm

end SafeLearning.CompleteFoundationsCubeRadiusAndNetMargin32
