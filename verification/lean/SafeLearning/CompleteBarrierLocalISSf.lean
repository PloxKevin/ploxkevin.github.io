import SafeLearning.CompleteBarrierAEComparison
import SafeLearning.CompleteBarrierFiniteEscape

set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace SafeLearning.CompleteBarrierLocalISSf
open SafeLearning.CompleteBarrierAEComparison

theorem genuine_boundary_nonpositive (M R d : ℝ)
    (hM : 0≤M) (hMR : M*R≤1) (hd : |d|≤R) : -M+M^2*d≤0 := by
  have hdR : d≤R := (le_abs_self d).trans hd
  have h1 := mul_le_mul_of_nonneg_left hdR (sq_nonneg M)
  have h2 := mul_le_mul_of_nonneg_left hMR hM
  nlinarith

/-- Invariance on every actual interval of a Caratheodory solution, including
arbitrary measurable essentially bounded disturbances. -/
theorem genuine_ae_local_inflated_set_invariance (x d : ℝ → ℝ) (M R T : ℝ)
    (hT : 0≤T) (hR : 0≤R) (hM : 0≤M) (hMR : M*R≤1)
    (hc : AbsolutelyContinuousOnInterval x 0 T)
    (hx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (-x t+x t^2*d t) t)
    (hd : ∀ᵐ t ∂volume, |d t|≤R) (h0 : x 0≤M) :
    ∀ t ∈ Icc 0 T, x t≤M := by
  obtain ⟨C,hC⟩ := hc.exists_bound
  let z : ℝ → ℝ := fun t => x t-M
  let v : ℝ → ℝ := fun t => -x t+x t^2*d t
  let L : ℝ := -1+(C+M)*R
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => M) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    fun_prop
  have hz : AbsolutelyContinuousOnInterval z 0 T := hc.sub hconst
  have hzder : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt z (v t) t := by
    filter_upwards [hx] with t hx ht
    exact (hx ht).sub_const M
  have hzbound : ∀ᵐ t ∂volume, t ∈ Icc 0 T → 0<z t → v t≤L*z t := by
    filter_upwards [hd] with t hd ht hzt
    have hxm : M<x t := by simpa [z] using hzt
    have hxC : x t≤C := (le_abs_self (x t)).trans (by
      simpa only [Real.norm_eq_abs] using hC t (by simpa [uIcc_of_le hT] using ht))
    have hdt : d t≤R := (le_abs_self (d t)).trans hd
    have hcoeff : -1+(x t+M)*d t≤L := by
      have h1 := mul_le_mul_of_nonneg_left hdt (by linarith : 0≤x t+M)
      have h2 := mul_le_mul_of_nonneg_right (by linarith : x t+M≤C+M) hR
      dsimp [L]
      linarith
    have hbd := genuine_boundary_nonpositive M R (d t) hM hMR hd
    have hmul := mul_le_mul_of_nonneg_left hcoeff (by linarith : 0≤x t-M)
    have heq : -x t+x t^2*d t = (-M+M^2*d t)+(x t-M)*(-1+(x t+M)*d t) := by ring
    dsimp [v,z]
    rw [heq]
    linarith
  have hi := genuine_ae_one_sided_invariance z v 0 T L hT hz hzder hzbound (by dsimp [z]; linarith)
  intro t ht
  have h := hi t ht
  dsimp [z] at h
  linarith

theorem genuine_quarter_radius_ae_invariance (x d : ℝ → ℝ) (R T : ℝ)
    (hT : 0≤T) (hR : 0≤R) (hR1 : R≤1/4)
    (hc : AbsolutelyContinuousOnInterval x 0 T)
    (hx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (-x t+x t^2*d t) t)
    (hd : ∀ᵐ t ∂volume, |d t|≤R) (h0 : x 0≤2+R) :
    ∀ t ∈ Icc 0 T, x t≤2+R := by
  have hprod : (2+R)*R≤(9/4)*(1/4) := mul_le_mul (by linarith) hR1 hR (by norm_num)
  exact genuine_ae_local_inflated_set_invariance x d (2+R) R T hT hR
    (by linarith) (by linarith) hc hx hd h0

def inflationSlope (bound : ℝ) : ℝ := (1-2*bound)/(2*bound^2)
def localInflation (bound r : ℝ) : ℝ := inflationSlope bound*r

theorem genuine_any_small_bound_inflation (bound : ℝ)
    (hb0 : 0<bound) (hb : bound<1/2) :
    0 < inflationSlope bound ∧
    ∀ r : ℝ, 0≤r → r≤bound → 0≤2+localInflation bound r ∧
      (2+localInflation bound r)*r<1 := by
  have hs : 0 < inflationSlope bound := div_pos (by linarith) (by positivity)
  refine ⟨hs,?_⟩
  intro r hr hrb
  have hgamma : 0≤localInflation bound r := mul_nonneg hs.le hr
  have hmono : localInflation bound r≤localInflation bound bound := mul_le_mul_of_nonneg_left hrb hs.le
  have heq : (2+localInflation bound bound)*bound=bound+1/2 := by
    dsimp [localInflation,inflationSlope]
    field_simp
    ring
  have hprod := mul_le_mul (by linarith : 2+localInflation bound r≤2+localInflation bound bound)
    hrb hr (by linarith : 0≤2+localInflation bound bound)
  rw [heq] at hprod
  exact ⟨by linarith,by linarith⟩

theorem genuine_local_inflation_class_K_infinity (bound : ℝ)
    (hb0 : 0<bound) (hb : bound<1/2) :
    Continuous (localInflation bound) ∧ localInflation bound 0=0 ∧
      StrictMono (localInflation bound) ∧ Tendsto (localInflation bound) atTop atTop := by
  have hs := (genuine_any_small_bound_inflation bound hb0 hb).1
  refine ⟨by unfold localInflation; fun_prop,by simp [localInflation],?_,?_⟩
  · intro a b hab
    exact mul_lt_mul_of_pos_left hab hs
  · change Tendsto (fun r => inflationSlope bound*r) atTop atTop
    simpa only [mul_comm,id_eq] using (tendsto_id : Tendsto (fun r : ℝ => r) atTop atTop).atTop_mul_const hs

theorem genuine_any_small_bound_ae_ISSf (x d : ℝ → ℝ) (bound R T : ℝ)
    (hb0 : 0<bound) (hb : bound<1/2) (hR : 0≤R) (hRb : R≤bound) (hT : 0≤T)
    (hc : AbsolutelyContinuousOnInterval x 0 T)
    (hx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (-x t+x t^2*d t) t)
    (hd : ∀ᵐ t ∂volume, |d t|≤R) (h0 : x 0≤2+localInflation bound R) :
    ∀ t ∈ Icc 0 T, x t≤2+localInflation bound R := by
  obtain ⟨hM,hMR⟩ := (genuine_any_small_bound_inflation bound hb0 hb).2 R hR hRb
  exact genuine_ae_local_inflated_set_invariance x d _ R T hT hR hM hMR.le hc hx hd h0

theorem genuine_actual_barrier_and_controller_identities (x d : ℝ) :
    HasDerivAt (fun s : ℝ => 2-s) (-1) x ∧
    (-1)*(-x)=x ∧ (-1)*x^2= -x^2 ∧
    -x+x^2*((-x^2)+d)= -x-x^4+x^2*d := by
  refine ⟨?_,by ring,by ring,by ring⟩
  convert (hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x) using 1 <;> (try ext s) <;> norm_num

theorem genuine_reciprocal_change_of_variable (x : ℝ → ℝ) (t : ℝ)
    (hne : x t≠0) (hd : HasDerivAt x (-x t+x t^2) t) :
    HasDerivAt (fun s => 1/x s) (1/x t-1) t := by
  convert hd.inv hne using 1
  · ext s
    simp [one_div]
  · field_simp
    ring

theorem genuine_nominal_safeguarding (x : ℝ → ℝ) (T : ℝ) (hT : 0≤T)
    (hc : AbsolutelyContinuousOnInterval x 0 T)
    (hx : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt x (-x t) t)
    (h0 : x 0≤2) : ∀ t ∈ Icc 0 T, x t≤2 := by
  apply genuine_ae_local_inflated_set_invariance x (fun _ => 0) 2 0 T hT
    (by norm_num) (by norm_num) (by norm_num) hc _ (by simp) h0
  filter_upwards [hx] with t hx ht
  simpa using hx ht

end SafeLearning.CompleteBarrierLocalISSf
