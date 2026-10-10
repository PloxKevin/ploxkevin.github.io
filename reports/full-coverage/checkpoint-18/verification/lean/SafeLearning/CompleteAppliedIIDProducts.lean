import SafeLearning.CompleteAppliedBinomialModel
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedIIDProducts
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

def iidProductLaw {Data : Type*} [MeasurableSpace Data] (n : ℕ) (P : Measure Data) :
    Measure (Fin n → Data) := Measure.pi (fun _ => P)

theorem actual_product_coordinate_laws {Data : Type*} [MeasurableSpace Data]
    (n : ℕ) (P : Measure Data) [IsProbabilityMeasure P] (i : Fin n) :
    HasLaw (fun sample:Fin n → Data => sample i) P (iidProductLaw n P) := by
  exact ⟨(measurable_pi_apply i).aemeasurable,
    (measurePreserving_eval (fun _:Fin n => P) i).map_eq⟩

theorem actual_product_coordinates_independent {Data : Type*} [MeasurableSpace Data]
    (n : ℕ) (P : Measure Data) [IsProbabilityMeasure P] :
    iIndepFun (fun i:Fin n => fun sample:Fin n → Data => sample i) (iidProductLaw n P) := by
  simpa only [iidProductLaw,id_eq] using
    (iIndepFun_pi (X := fun _:Fin n => (id:Data → Data))
      (μ := fun _:Fin n => P) (fun _ => aemeasurable_id))

theorem actual_iid_training_law {Ω Data : Type*} [MeasurableSpace Ω] [MeasurableSpace Data]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) (P : Measure Data)
    [IsProbabilityMeasure P] (X : Fin n → Ω → Data) (hind : iIndepFun X μ)
    (hLaw : ∀ i,HasLaw (X i) P μ) :
    HasLaw (fun omega i => X i omega) (iidProductLaw n P) μ := hind.hasLaw_pi hLaw

theorem actual_training_event_probability {Ω Data : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Data] (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ)
    (P : Measure Data) [IsProbabilityMeasure P] (X : Fin n → Ω → Data)
    (hind : iIndepFun X μ) (hLaw : ∀ i,HasLaw (X i) P μ)
    (E : Set (Fin n → Data)) (hE : MeasurableSet E) :
    μ.real {omega | (fun i => X i omega)∈E}=(iidProductLaw n P).real E := by
  exact (actual_iid_training_law μ n P X hind hLaw).measureReal_eq hE

theorem actual_bernoulli_atom_probabilities (p : unitInterval) :
    (bernoulliMeasure (1:ℝ) 0 p).real {1}=(p:ℝ) ∧
      (bernoulliMeasure (1:ℝ) 0 p).real {0}=1-(p:ℝ) := by
  simp [bernoulliMeasure_real_apply,unitInterval.coe_symm_eq]

theorem actual_bernoulli_mean_and_variance (p : unitInterval) :
    (∫ z:ℝ,z ∂bernoulliMeasure (1:ℝ) 0 p)=(p:ℝ) ∧
      variance (id:ℝ → ℝ) (bernoulliMeasure (1:ℝ) 0 p)=(p:ℝ)*(1-(p:ℝ)) := by
  have hi : (∫ z:ℝ,z ∂bernoulliMeasure (1:ℝ) 0 p)=(p:ℝ) := by
    rw [integral_bernoulliMeasure]
    simp
  refine ⟨hi,?_⟩
  rw [variance_eq_integral aemeasurable_id]
  change (∫ z:ℝ,(z-(∫ y:ℝ,y ∂bernoulliMeasure (1:ℝ) 0 p))^2
    ∂bernoulliMeasure (1:ℝ) 0 p)=_
  rw [hi,integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  ring

theorem actual_indicator_has_source_bernoulli_law {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    (p : unitInterval) (hp : μ.real A=(p:ℝ)) :
    HasLaw (A.indicator (fun _ => (1:ℝ))) (bernoulliMeasure (1:ℝ) 0 p) μ := by
  have h := hasLaw_indicator_one_bernoulliMeasure (M := ℝ) (P := μ) (s := A)
    hA.nullMeasurableSet
  have he : (⟨μ.real A,by simp⟩:unitInterval)=p := Subtype.ext hp
  have hf : A.indicator (1:Ω → ℝ)=A.indicator (fun _ => (1:ℝ)) := by
    funext omega
    rfl
  rw [hf,he] at h
  exact h

theorem zero_factorial_convention : Nat.factorial 0=1 := rfl

end SafeLearning.CompleteAppliedIIDProducts
