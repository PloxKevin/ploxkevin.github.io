import SafeLearning.CompleteAppliedFiniteEntropy
set_option autoImplicit false
noncomputable section
namespace SafeLearning.CompleteAppliedFiniteBregman
open MeasureTheory InformationTheory
open SafeLearning.CompleteAppliedFiniteKLSupport SafeLearning.CompleteAppliedFiniteEntropy
open scoped ENNReal BigOperators

def negativeEntropy {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i,x i*Real.log (x i)
def entropyDerivative {n : ℕ} (q : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i,(Real.log (q i)+1) • ContinuousLinearMap.proj i

theorem actual_negative_entropy_frechet_derivative {n : ℕ}
    (q : Fin n → ℝ) (hq : ∀ i,q i≠0) :
    HasFDerivAt negativeEntropy (entropyDerivative q) q := by
  unfold negativeEntropy entropyDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  have hd : HasDerivAt (fun z : ℝ => z*Real.log z) (Real.log (q i)+1) (q i) :=
    Real.hasDerivAt_mul_log (hq i)
  simpa only [Function.comp_def] using
    hd.comp_hasFDerivAt q (hasFDerivAt_apply (𝕜:=ℝ) i q)

theorem actual_entropy_derivative_linear_action {n : ℕ}
    (q x : Fin n → ℝ) : entropyDerivative q x=∑ i,(Real.log (q i)+1)*x i := by
  simp [entropyDerivative]

def entropyBregman {n : ℕ} (p q : Fin n → ℝ) : ℝ :=
  negativeEntropy p-negativeEntropy q-entropyDerivative q (p-q)

theorem actual_finite_KL_is_entropy_bregman {n : ℕ} (p q : PMF (Fin n))
    (hq : ∀ i,q i≠0) :
    entropyBregman (fun i=>(p i).toReal) (fun i=>(q i).toReal)=
      (klDiv p.toMeasure q.toMeasure).toReal := by
  have hs:∀ i,p i≠0 → q i≠0:=fun i _=>hq i
  rw [actual_support_kl_sum p q hs,entropyBregman,actual_entropy_derivative_linear_action]
  have hlog (i : Fin n) : (p i).toReal*Real.log ((p i).toReal/(q i).toReal)=
      (p i).toReal*Real.log (p i).toReal-(p i).toReal*Real.log (q i).toReal := by
    by_cases hp:(p i).toReal=0
    · simp [hp]
    · have hqr:(q i).toReal≠0:=by
        intro hz
        have hx : q i=0 ∨ q i=⊤ := by simpa only [ENNReal.toReal_eq_zero_iff] using hz
        rcases hx with hzero | htop
        · exact hq i hzero
        · exact q.apply_ne_top i htop
      rw [Real.log_div hp hqr]
      ring
  simp only [hlog,negativeEntropy,Pi.sub_apply,Finset.sum_sub_distrib]
  have he: (∑ i,(Real.log (q i).toReal+1)*((p i).toReal-(q i).toReal))=
      (∑ i,(p i).toReal*Real.log (q i).toReal)-
      (∑ i,(q i).toReal*Real.log (q i).toReal) := by
    calc
      _=∑ i,((p i).toReal*Real.log (q i).toReal-
          (q i).toReal*Real.log (q i).toReal+(p i).toReal-(q i).toReal) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=_ := by rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,
        Finset.sum_sub_distrib,actual_finite_weights_sum,actual_finite_weights_sum];ring
  rw [he]
  ring

theorem actual_finite_bregman_nonnegative_and_identity {n : ℕ}
    (p q : PMF (Fin n)) (hq : ∀ i,q i≠0) :
    0≤entropyBregman (fun i=>(p i).toReal) (fun i=>(q i).toReal) ∧
    (entropyBregman (fun i=>(p i).toReal) (fun i=>(q i).toReal)=0 ↔ p=q) := by
  rw [actual_finite_KL_is_entropy_bregman p q hq]
  have hs:∀ i,p i≠0 → q i≠0:=fun i _=>hq i
  have hf:=klDiv_ne_top ((actual_support_absolute_continuity p q).mpr hs) Integrable.of_finite
  exact ⟨ENNReal.toReal_nonneg,by
    rw [ENNReal.toReal_eq_zero_iff]
    simp only [hf,or_false,actual_finite_gibbs_equality]⟩

end SafeLearning.CompleteAppliedFiniteBregman
