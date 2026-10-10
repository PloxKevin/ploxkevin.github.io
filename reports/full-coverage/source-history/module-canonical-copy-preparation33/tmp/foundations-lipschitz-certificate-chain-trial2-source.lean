import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped NNReal
namespace SafeLearning.CompleteFoundationsLipschitzCertificateChain

theorem actual_one_sided_absolute_value_chain (value anchor allowance : ℝ)
    (hbound : |value-anchor|≤allowance) :
    value=anchor+(value-anchor) ∧
    -|value-anchor|≤value-anchor ∧
    -allowance≤ -|value-anchor| ∧ anchor-allowance≤value := by
  have ha := neg_abs_le (value-anchor)
  refine ⟨by ring,ha,by linarith,?_⟩
  linarith

theorem actual_real_global_lipschitz_source_certificate_chain
    (f : ℝ → ℝ) (L x anchor threshold : ℝ)
    (hlip : ∀ a b,|f a-f b|≤L*|a-b|)
    (hcertificate : threshold≤f anchor-L*|x-anchor|) :
    f x=f anchor+(f x-f anchor) ∧
    f anchor-L*|x-anchor|≤f x ∧ threshold≤f x := by
  have h := actual_one_sided_absolute_value_chain (f x) (f anchor)
    (L*|x-anchor|) (hlip x anchor)
  exact ⟨h.1,h.2.2.2,hcertificate.trans h.2.2.2⟩

theorem actual_relative_domain_lipschitz_source_certificate
    (domain : Set ℝ) (f : ℝ → ℝ) (L x anchor threshold : ℝ)
    (hx : x∈domain) (ha : anchor∈domain)
    (hlip : ∀ a∈domain,∀ b∈domain,|f a-f b|≤L*|a-b|)
    (hcertificate : threshold≤f anchor-L*|x-anchor|) : threshold≤f x := by
  have h := actual_one_sided_absolute_value_chain (f x) (f anchor)
    (L*|x-anchor|) (hlip x hx anchor ha)
  exact hcertificate.trans h.2.2.2

theorem actual_mathlib_lipschitz_predicate_gives_the_literal_certificate
    (f : ℝ → ℝ) (L : ℝ≥0) (hlip : LipschitzWith L f)
    (x anchor threshold : ℝ)
    (hcertificate : threshold≤f anchor-(L:ℝ)*|x-anchor|) : threshold≤f x := by
  have h (a b : ℝ) : |f a-f b|≤(L:ℝ)*|a-b| := by
    simpa only [Real.dist_eq] using hlip.dist_le_mul a b
  exact (actual_real_global_lipschitz_source_certificate_chain f L x anchor threshold
    h hcertificate).2.2

theorem actual_literal_two_point_five_one_and_one_point_five_certificate
    (f : ℝ → ℝ) (x anchor : ℝ)
    (hlip : ∀ a b,|f a-f b|≤1*|a-b|)
    (ha : f anchor=5/2) (hd : |x-anchor|=3/2) :
    1≤f x ∧ (0:ℝ)≤f x := by
  have h := actual_real_global_lipschitz_source_certificate_chain f 1 x anchor 1
    hlip (by rw [ha,hd];norm_num)
  exact ⟨h.2.2,by linarith [h.2.2]⟩

end SafeLearning.CompleteFoundationsLipschitzCertificateChain
