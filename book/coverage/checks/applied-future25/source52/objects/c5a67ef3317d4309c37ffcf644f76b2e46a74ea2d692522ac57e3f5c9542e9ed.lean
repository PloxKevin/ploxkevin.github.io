import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace SafeLearning.CompleteFoundationsMinimaModels
open Set Filter
open scoped Topology

abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def linearSum (u : E) : ℝ := u 0+u 1
def feasible : Set E := {u | 1≤linearSum u}
def sublevel (c : ℝ) : Set ℝ := {x | x^2/(1+x^2)≤c}

theorem actual_compact_continuous_minimum {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K) (hne : K.Nonempty) (f : X→ℝ)
    (hf : ContinuousOn f K) : ∃ x∈K,IsMinOn f K x := hK.exists_isMinOn hne hf

theorem actual_closed_coercive_minimum {X : Type*} [TopologicalSpace X]
    (S : Set X) (hs : IsClosed S) (x₀ : X) (hx : x₀∈S) (f : X→ℝ)
    (hf : ContinuousOn f S) (hc : Tendsto f (cocompact X ⊓ 𝓟 S) atTop) :
    ∃ x∈S,IsMinOn f S x :=
  hf.exists_isMinOn' hs hx (hc.eventually (eventually_ge_atTop (f x₀)))

theorem actual_exp_infimum_and_no_minimum :
    IsGLB ((fun x : ℝ=>Real.exp (-x)) '' Ici 0) 0 ∧
    ¬∃ x∈Ici (0:ℝ),IsMinOn (fun y=>Real.exp (-y)) (Ici 0) x := by
  have ht : Tendsto (fun n : ℕ=>Real.exp (-(n:ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  constructor
  · constructor
    · rintro y ⟨x,hx,rfl⟩;exact (Real.exp_pos _).le
    · intro b hb
      exact le_of_tendsto_of_tendsto tendsto_const_nhds ht
        (Eventually.of_forall (fun n=>hb ⟨(n:ℝ),by simpa using Nat.cast_nonneg (α:=ℝ) n,rfl⟩))
  · rintro ⟨x,hx,hm⟩
    have hx' : 0≤x := hx
    have h := hm (show x+1∈Ici (0:ℝ) by change 0≤x+1;linarith)
    have he : Real.exp (-(x+1))<Real.exp (-x) := Real.exp_lt_exp.mpr (by linarith)
    exact (not_le.mpr he) h

theorem actual_interval_quadratic_derivative (x : ℝ) :
    HasDerivAt (fun y : ℝ=>y^2-y) (2*x-1) x := by
  convert ((hasDerivAt_id x).pow 2).sub (hasDerivAt_id x) using 1 <;>
    (first | rfl | norm_num | (simp only [id_eq];ring))

theorem actual_interval_quadratic_minimum :
    IsCompact (Icc (0:ℝ) 1) ∧ Continuous (fun x : ℝ=>x^2-x) ∧
    (1/2:ℝ)∈Icc (0:ℝ) 1 ∧
    (∀ x : ℝ,-1/4≤x^2-x ∧ (x^2-x= -1/4↔x=1/2)) := by
  refine ⟨isCompact_Icc,(continuous_id.pow 2).sub continuous_id,by norm_num,?_⟩
  intro x
  constructor
  · nlinarith [sq_nonneg (x-1/2)]
  · constructor
    · intro h;nlinarith [sq_nonneg (x-1/2)]
    · rintro rfl;norm_num

theorem actual_norm_squared (u : E) : ‖u‖^2=(u 0)^2+(u 1)^2 := by
  have hi (v w : E) : inner ℝ v w=v 0*w 0+v 1*w 1 := by
    simp [PiLp.inner_apply,Fin.sum_univ_succ]
    ring
  rw [← real_inner_self_eq_norm_sq,hi u u]
  ring

theorem actual_halfspace_closed_nonempty : IsClosed feasible ∧ feasible.Nonempty := by
  constructor
  · exact isClosed_Ici.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 0).add
      (PiLp.continuous_apply 2 (fun _ : Fin 2=>ℝ) 1))
  · exact ⟨point (1/2) (1/2),by norm_num [feasible,linearSum,point]⟩

theorem actual_norm_squared_coercive :
    Tendsto (fun u : E=>‖u‖^2) (cocompact E) atTop :=
  (tendsto_pow_atTop (by decide : (2:ℕ)≠0)).comp tendsto_norm_cocompact_atTop

theorem actual_halfspace_norm_unique_minimum (u : E) (hu : u∈feasible) :
    (1/2:ℝ)≤‖u‖^2 ∧ (‖u‖^2=1/2↔u=point (1/2) (1/2)) := by
  have hf : 1≤u 0+u 1 := hu
  rw [actual_norm_squared]
  constructor
  · nlinarith [sq_nonneg (u 0-u 1)]
  · constructor
    · intro he
      have hsum : u 0+u 1=1 := by nlinarith [sq_nonneg (u 0-u 1)]
      have hdiff : u 0=u 1 := by nlinarith [sq_nonneg (u 0-u 1)]
      ext i;fin_cases i <;> simp [point] <;> linarith
    · rintro rfl;norm_num [point]

theorem actual_linear_objective_unbounded :
    (∀ B : ℝ,∃ u : E,B<linearSum u) ∧
    ¬∃ u : E,∀ v : E,linearSum v≤linearSum u := by
  have h (B : ℝ) : B<linearSum (point (B/2+1) (B/2+1)) := by
    norm_num [linearSum,point];linarith
  refine ⟨fun B=>⟨_,h B⟩,?_⟩
  rintro ⟨u,hu⟩
  exact (not_le.mpr (h (linearSum u))) (hu _)

theorem actual_sublevel_value_range (x : ℝ) :
    0≤x^2/(1+x^2) ∧ x^2/(1+x^2)<1 := by
  have hd : 0<1+x^2 := by positivity
  constructor
  · positivity
  · rw [div_lt_iff₀ hd];linarith

theorem actual_sublevel_below_one (c : ℝ) (hc : c<1) :
    sublevel c={x : ℝ | x^2≤c/(1-c)} := by
  ext x
  have hd : 0<1+x^2 := by positivity
  have he : 0<1-c := by linarith
  simp only [sublevel,mem_setOf_eq]
  rw [div_le_iff₀ hd,le_div_iff₀ he]
  constructor <;> intro h <;> nlinarith

theorem actual_sublevel_interval (c : ℝ) (h0 : 0≤c) (h1 : c<1) :
    sublevel c=Icc (-Real.sqrt (c/(1-c))) (Real.sqrt (c/(1-c))) := by
  rw [actual_sublevel_below_one c h1]
  ext x
  exact Real.sq_le (div_nonneg h0 (by linarith))

theorem actual_sublevel_negative_empty (c : ℝ) (hc : c<0) : sublevel c=∅ := by
  ext x
  simp only [sublevel,mem_setOf_eq,mem_empty_iff_false,iff_false]
  exact not_le.mpr (lt_of_lt_of_le hc (actual_sublevel_value_range x).1)

theorem actual_sublevel_at_least_one (c : ℝ) (hc : 1≤c) : sublevel c=univ := by
  ext x
  simp only [sublevel,mem_setOf_eq,mem_univ,iff_true]
  exact (actual_sublevel_value_range x).2.le.trans hc

theorem actual_sublevel_compact_iff (c : ℝ) : IsCompact (sublevel c)↔c<1 := by
  constructor
  · intro h
    by_contra hc
    rw [actual_sublevel_at_least_one c (le_of_not_gt hc)] at h
    exact not_bddAbove_univ h.bddAbove
  · intro hc
    by_cases hn : c<0
    · rw [actual_sublevel_negative_empty c hn];exact isCompact_empty
    · rw [actual_sublevel_interval c (le_of_not_gt hn) hc];exact isCompact_Icc

theorem actual_sublevel_function_limit :
    Tendsto (fun x : ℝ=>x^2/(1+x^2)) atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ=>x^2/(1+x^2)) atBot (𝓝 1) := by
  have hsq : Tendsto (fun x : ℝ=>x^2) atTop atTop := tendsto_pow_atTop (by decide)
  have hi : Tendsto (fun x : ℝ=>(1+x^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left atTop 1 hsq)
  have ht : Tendsto (fun x : ℝ=>1-(1+x^2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hi
  have he : (fun x : ℝ=>x^2/(1+x^2))=(fun x : ℝ=>1-(1+x^2)⁻¹) := by
    funext x
    have h : 1+x^2≠0 := ne_of_gt (by positivity)
    field_simp;ring
  constructor
  · rw [he];exact ht
  · have h := (he ▸ ht).comp tendsto_neg_atBot_atTop
    simpa [Function.comp_def] using h

end SafeLearning.CompleteFoundationsMinimaModels
