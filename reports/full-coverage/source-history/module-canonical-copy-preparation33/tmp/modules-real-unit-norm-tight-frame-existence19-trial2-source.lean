import SafeLearning.CompleteModulesRealHarmonicOddFrames
import SafeLearning.CompleteModulesRealHarmonicFrequencyChoices
import SafeLearning.CompleteModulesRealTightFrameTransport
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
open Matrix
open scoped BigOperators
namespace SafeLearning.CompleteModulesRealUnitNormTightFrameExistence
open CompleteModulesRealHarmonicPairedFrames CompleteModulesRealHarmonicOddFrames
  CompleteModulesRealHarmonicFrequencyChoices CompleteModulesRealTightFrameTransport
variable {T D : Type*} [Fintype T] [Fintype D] [DecidableEq D]

theorem actual_square_identity_is_a_real_unit_norm_tight_frame [Nonempty D] :
    (∀ t : D,‖(WithLp.toLp 2 (fun i => (1 : Matrix D D ℝ) t i) : EuclideanSpace ℝ D)‖=1) ∧
    (1 : Matrix D D ℝ)ᵀ*1=
      ((Fintype.card D:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ) := by
  constructor
  · intro t
    have hs : ‖(WithLp.toLp 2 (fun i => (1 : Matrix D D ℝ) t i) : EuclideanSpace ℝ D)‖^2=1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Matrix.one_apply]
    nlinarith [norm_nonneg (WithLp.toLp 2 (fun i => (1 : Matrix D D ℝ) t i) : EuclideanSpace ℝ D)]
  · have hd : (Fintype.card D:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
    simp [hd]

theorem actual_real_unit_norm_tight_frames_exist_for_every_positive_dimension_below_the_sample_count
    [Nonempty D] (hOrder : Fintype.card D ≤ Fintype.card T) :
    ∃ X : Matrix T D ℝ,
      (∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ D)‖=1) ∧
      Xᵀ*X=((Fintype.card T:ℝ)/(Fintype.card D:ℝ)) • (1 : Matrix D D ℝ) := by
  have hd : 0<Fintype.card D := Fintype.card_pos
  by_cases heq : Fintype.card D=Fintype.card T
  · let eT : T ≃ D := Fintype.equivOfCardEq heq.symm
    exact actual_unit_norm_tight_frames_transport_across_both_index_equivalences
      (1 : Matrix D D ℝ) eT (Equiv.refl D)
      actual_square_identity_is_a_real_unit_norm_tight_frame.1
      actual_square_identity_is_a_real_unit_norm_tight_frame.2
  · have hlt : Fintype.card D<Fintype.card T := by omega
    have hn : Fintype.card T≠0 := by omega
    letI : NeZero (Fintype.card T) := ⟨hn⟩
    let eT : T ≃ ZMod (Fintype.card T) := Fintype.equivOfCardEq (by simp)
    obtain ⟨m,heven|hodd⟩ := Nat.even_or_odd' (Fintype.card D)
    · have hm : 0 < m := by omega
      letI : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
      have hRange : 2*m < Fintype.card T := by omega
      let eD : D ≃ Fin m × Fin 2 := Fintype.equivOfCardEq (by
        simp only [Fintype.card_prod,Fintype.card_fin]
        omega)
      exact actual_unit_norm_tight_frames_transport_across_both_index_equivalences
        (pairedFrame (selectedFrequency (Fintype.card T) m)) eT eD
        (actual_paired_harmonic_inputs_have_unit_euclidean_norm _)
        (actual_paired_harmonic_design_has_the_uniform_tight_frame_gram _
          (actual_selected_positive_frequencies_are_distinct _ _ hRange)
          (actual_no_selected_frequency_pair_sums_to_zero _ _ hRange))
    · have hRange : 2*m < Fintype.card T := by omega
      let eD : D ≃ Unit ⊕ (Fin m × Fin 2) := Fintype.equivOfCardEq (by
        simp only [Fintype.card_sum,Fintype.card_unit,Fintype.card_prod,Fintype.card_fin]
        omega)
      exact actual_unit_norm_tight_frames_transport_across_both_index_equivalences
        (oddFrame (selectedFrequency (Fintype.card T) m)) eT eD
        (actual_odd_harmonic_inputs_have_unit_euclidean_norm _)
        (actual_odd_harmonic_design_has_the_uniform_tight_frame_gram _
          (actual_selected_positive_frequencies_are_distinct _ _ hRange)
          (actual_no_selected_frequency_pair_sums_to_zero _ _ hRange)
          (actual_selected_positive_frequencies_are_nonzero _ _ hRange))

theorem actual_arbitrary_positive_integer_dimensions_have_real_unit_norm_tight_frames
    (d n : ℕ) (hd : 0<d) (hOrder : d≤n) :
    ∃ X : Matrix (Fin n) (Fin d) ℝ,
      (∀ t,‖(WithLp.toLp 2 (fun i => X t i) : EuclideanSpace ℝ (Fin d))‖=1) ∧
      Xᵀ*X=((n:ℝ)/(d:ℝ)) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  simpa only [Fintype.card_fin] using
    actual_real_unit_norm_tight_frames_exist_for_every_positive_dimension_below_the_sample_count
      (T:=Fin n) (D:=Fin d) (by simpa only [Fintype.card_fin] using hOrder)

end SafeLearning.CompleteModulesRealUnitNormTightFrameExistence
