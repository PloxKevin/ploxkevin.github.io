import SafeLearning.CompleteModulesLandscapeMaximalEndpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Metric
open scoped Topology NNReal

namespace SafeLearning.CompleteModulesLandscapeMaximalExistence

open SafeLearning.CompleteModulesLandscapeMaximalEndpoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual forward solution with a positive extended-real upper endpoint. -/
structure ForwardSolution (f : E → E) (D : Set E) (x₀ : E) where
  endpoint : EReal
  endpoint_pos : 0 < endpoint
  path : ℝ → E
  initial : path 0 = x₀
  in_domain : MapsTo path (forwardTimeDomain endpoint) D
  ode : ∀ t ∈ forwardTimeDomain endpoint,
    HasDerivWithinAt path (f (path t)) (forwardTimeDomain endpoint) t

namespace ForwardSolution

variable {f : E → E} {D : Set E} {x₀ : E}

/-- Extension preserves every value on the old time domain. -/
def Extends (p q : ForwardSolution f D x₀) : Prop :=
  p.endpoint ≤ q.endpoint ∧ EqOn p.path q.path (forwardTimeDomain p.endpoint)

theorem extends_refl (p : ForwardSolution f D x₀) : Extends p p :=
  ⟨le_rfl,fun _ _ => rfl⟩

theorem extends_trans {p q r : ForwardSolution f D x₀}
    (hpq : Extends p q) (hqr : Extends q r) : Extends p r :=
  ⟨hpq.1.trans hqr.1,fun _ ht =>
    (hpq.2 ht).trans (hqr.2 (forwardTimeDomain_mono hpq.1 ht))⟩

/-- A compatible chain of true forward solutions has a true solution upper
bound. Its endpoint is the supremum, and its derivative is verified locally
against a chain member whose domain contains the time in question. -/
theorem actual_nonempty_chain_has_a_forward_solution_upper_bound
    (c : Set (ForwardSolution f D x₀)) (hc : IsChain Extends c) (hne : c.Nonempty) :
    ∃ u : ForwardSolution f D x₀, ∀ p ∈ c, Extends p u := by
  classical
  let B : EReal := sSup (endpoint '' c)
  have hle : ∀ p ∈ c, p.endpoint ≤ B := by
    intro p hp
    exact le_sSup (mem_image_of_mem endpoint hp)
  have hB : 0 < B := by
    obtain ⟨p,hp⟩ := hne
    exact p.endpoint_pos.trans_le (hle p hp)
  have hex : ∀ t ∈ forwardTimeDomain B,
      ∃ p ∈ c, t ∈ forwardTimeDomain p.endpoint := by
    intro t ht
    obtain ⟨b,⟨p,hp,rfl⟩,hb⟩ := lt_sSup_iff.mp ht.2
    exact ⟨p,hp,ht.1,hb⟩
  let Y : ℝ → E := fun t =>
    if ht : t ∈ forwardTimeDomain B then (Classical.choose (hex t ht)).path t else x₀
  have hagree : ∀ p ∈ c, EqOn p.path Y (forwardTimeDomain p.endpoint) := by
    intro p hp t ht
    have htB : t ∈ forwardTimeDomain B := forwardTimeDomain_mono (hle p hp) ht
    let q := Classical.choose (hex t htB)
    have hq : q ∈ c ∧ t ∈ forwardTimeDomain q.endpoint := Classical.choose_spec (hex t htB)
    change p.path t = (if ht' : t ∈ forwardTimeDomain B then
      (Classical.choose (hex t ht')).path t else x₀)
    rw [dite_eq_left htB]
    change p.path t = q.path t
    by_cases heq : p = q
    · simp only [heq]
    · rcases hc hp hq.1 heq with hpq | hqp
      · exact hpq.2 ht
      · exact (hqp.2 hq.2).symm
  have hYinitial : Y 0 = x₀ := by
    obtain ⟨p,hp⟩ := hne
    have h0 : (0 : ℝ) ∈ forwardTimeDomain p.endpoint := ⟨le_rfl,p.endpoint_pos⟩
    exact (hagree p hp h0).symm.trans p.initial
  have hYD : MapsTo Y (forwardTimeDomain B) D := by
    intro t ht
    obtain ⟨p,hp,htp⟩ := hex t ht
    rw [← hagree p hp htp]
    exact p.in_domain htp
  have hYODE : ∀ t ∈ forwardTimeDomain B,
      HasDerivWithinAt Y (f (Y t)) (forwardTimeDomain B) t := by
    intro t ht
    obtain ⟨p,hp,htp⟩ := hex t ht
    have hbound : {r : ℝ | (r : EReal) < p.endpoint} ∈ 𝓝 t :=
      (isOpen_lt continuous_coe_real_ereal continuous_const).mem_nhds htp.2
    have hold : forwardTimeDomain p.endpoint ∈ 𝓝[forwardTimeDomain B] t := by
      filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hbound] with r hr hrbound
      exact ⟨hr.1,hrbound⟩
    have he : Y =ᶠ[𝓝[forwardTimeDomain B] t] p.path := by
      filter_upwards [hold] with r hr
      exact (hagree p hp hr).symm
    rw [← hagree p hp htp]
    exact ((p.ode t htp).mono_of_mem_nhdsWithin hold).congr_of_eventuallyEq he
      (hagree p hp htp).symm
  let u : ForwardSolution f D x₀ := ⟨B,hB,Y,hYinitial,hYD,hYODE⟩
  exact ⟨u,fun p hp => ⟨hle p hp,hagree p hp⟩⟩

end ForwardSolution

variable [CompleteSpace E]

/-- Local Picard existence supplies a nonempty type of actual forward solutions. -/
theorem actual_forward_solution_exists_locally
    (f : E → E) (D : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (x₀ : E) (hx₀ : x₀ ∈ D) : Nonempty (ForwardSolution f D x₀) := by
  obtain ⟨ε,hε,x,hinit,hxD,hderiv⟩ :=
    SafeLearning.CompleteModulesLandscapeLocalExistence.actual_locally_lipschitz_autonomous_field_on_an_open_domain_has_a_local_solution
      f D hD hf x₀ hx₀ 0
  refine ⟨⟨(ε : EReal),EReal.coe_pos.mpr hε,x,hinit,?_,?_⟩⟩
  · intro t ht
    exact hxD t
  · intro t ht
    have hinterval : t ∈ Ico 0 ε := by simpa only [forwardTimeDomain_coe] using ht
    exact (hderiv t ⟨by linarith [hinterval.1],by simpa only [zero_add] using hinterval.2⟩).hasDerivWithinAt

/-- Every initial state in the open domain of a locally Lipschitz autonomous
field admits an actual forward maximal solution. Zorn's lemma is applied to
true solutions ordered by extension; maximal existence is not assumed. -/
theorem actual_locally_lipschitz_field_has_a_forward_maximal_solution_from_every_domain_point
    (f : E → E) (D : Set E) (hD : IsOpen D) (hf : LocallyLipschitzOn D f)
    (x₀ : E) (hx₀ : x₀ ∈ D) :
    ∃ B : EReal, 0 < B ∧ ∃ x : ℝ → E, x 0 = x₀ ∧
      MapsTo x (forwardTimeDomain B) D ∧
      (∀ t ∈ forwardTimeDomain B,
        HasDerivWithinAt x (f (x t)) (forwardTimeDomain B) t) ∧
      IsForwardMaximal f D x B := by
  classical
  let : Nonempty (ForwardSolution f D x₀) := actual_forward_solution_exists_locally f D hD hf x₀ hx₀
  obtain ⟨m,hm⟩ := exists_maximal_of_nonempty_chains_bounded
    (α := ForwardSolution f D x₀) (r := ForwardSolution.Extends)
    (fun c hc hne => ForwardSolution.actual_nonempty_chain_has_a_forward_solution_upper_bound c hc hne)
    ForwardSolution.extends_trans
  refine ⟨m.endpoint,m.endpoint_pos,m.path,m.initial,m.in_domain,m.ode,?_⟩
  intro S hlong hlonger
  obtain ⟨y,hEq,hyD,hyODE⟩ := hlonger
  have hS : (0 : EReal) < (S : EReal) := m.endpoint_pos.trans hlong
  have h0 : (0 : ℝ) ∈ forwardTimeDomain m.endpoint := ⟨le_rfl,m.endpoint_pos⟩
  let q : ForwardSolution f D x₀ := {
    endpoint := (S : EReal)
    endpoint_pos := hS
    path := y
    initial := (hEq h0).symm.trans m.initial
    in_domain := by simpa only [forwardTimeDomain_coe] using hyD
    ode := by simpa only [forwardTimeDomain_coe] using hyODE }
  have hmq : ForwardSolution.Extends m q := ⟨hlong.le,hEq⟩
  exact (not_le_of_gt hlong) (hm q hmq).1

end SafeLearning.CompleteModulesLandscapeMaximalExistence
