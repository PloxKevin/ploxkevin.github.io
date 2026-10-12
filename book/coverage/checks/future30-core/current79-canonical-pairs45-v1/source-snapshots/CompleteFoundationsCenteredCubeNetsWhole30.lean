import Mathlib

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators Topology NNReal
namespace SafeLearning.CompleteFoundationsCenteredCubeNetsWhole30

def unitCube (d : ℕ) : Set (EuclideanSpace ℝ (Fin d)) := {x | ∀ i, x i ∈ Icc (0 : ℝ) 1}
def center (d N : ℕ) (k : Fin d → Fin N) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ((k i : ℕ) + (1/2 : ℝ))/(N : ℝ))
def centeredGrid (d N : ℕ) : Finset (EuclideanSpace ℝ (Fin d)) := by
  classical
  exact Finset.univ.image (center d N)
def radius (d N : ℕ) : ℝ := Real.sqrt d/(2*(N : ℝ))
def IsFiniteNet {E : Type*} [PseudoMetricSpace E] (X : Set E) (Z : Finset E) (τ : ℝ) : Prop :=
  (∀ z ∈ Z, z ∈ X) ∧ ∀ x ∈ X, ∃ z ∈ Z, dist x z ≤ τ

theorem centered_coordinate_cover (N : ℕ) (hN : 0 < N) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ k : Fin N, |x - ((k : ℕ)+(1/2 : ℝ))/(N : ℝ)| ≤ 1/(2*(N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hx1 : x < 1
  · have hk : Nat.floor ((N : ℝ)*x) < N := by
      apply (Nat.floor_lt (mul_nonneg hNr.le hx.1)).mpr
      nlinarith
    refine ⟨⟨Nat.floor ((N : ℝ)*x),hk⟩,?_⟩
    have h₁ := Nat.floor_le (mul_nonneg hNr.le hx.1)
    have h₂ := Nat.lt_floor_add_one ((N : ℝ)*x)
    have hb : |(N : ℝ)*x-((Nat.floor ((N : ℝ)*x) : ℝ)+1/2)| ≤ 1/2 := by
      rw [abs_le]
      constructor <;> linarith
    have hid : x-((Nat.floor ((N : ℝ)*x) : ℝ)+1/2)/(N : ℝ)=
        ((N : ℝ)*x-((Nat.floor ((N : ℝ)*x) : ℝ)+1/2))/(N : ℝ) := by field_simp
    change |x-((Nat.floor ((N : ℝ)*x) : ℝ)+1/2)/(N : ℝ)| ≤ _
    rw [hid,abs_div,abs_of_pos hNr]
    calc
      _ ≤ (1/2)/(N : ℝ) := div_le_div_of_nonneg_right hb hNr.le
      _ = _ := by ring
  · have he : x=1 := by linarith [hx.2]
    refine ⟨⟨N-1,by omega⟩,?_⟩
    rw [he]
    have hc : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by rw [Nat.cast_sub (by omega)];norm_num
    change |1-(((N-1 : ℕ) : ℝ)+1/2)/(N : ℝ)| ≤ _
    rw [hc]
    have hi : 1-((N : ℝ)-1+1/2)/(N : ℝ)=1/(2*(N : ℝ)) := by field_simp;ring
    rw [hi,abs_of_pos (by positivity)]

theorem centered_point_injective (d N : ℕ) (hN : 0 < N) : Function.Injective (center d N) := by
  intro k l h
  funext i
  have he := congrArg (fun x : EuclideanSpace ℝ (Fin d) => x i) h
  change ((k i : ℕ)+(1/2 : ℝ))/(N : ℝ)=((l i : ℕ)+(1/2 : ℝ))/(N : ℝ) at he
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hc : ((k i : ℕ) : ℝ)=((l i : ℕ) : ℝ) := by field_simp at he;linarith
  apply Fin.ext
  exact_mod_cast hc

theorem actual_centered_grid_cardinality (d N : ℕ) (hN : 0 < N) :
    (centeredGrid d N).card=N^d := by
  classical
  rw [centeredGrid,Finset.card_image_of_injective _ (centered_point_injective d N hN)]
  simp

theorem actual_centered_point_in_cube (d N : ℕ) (hN : 0 < N) (k : Fin d → Fin N) :
    center d N k ∈ unitCube d := by
  have hNr : (0 : ℝ)<N := by exact_mod_cast hN
  intro i
  change ((k i : ℕ)+(1/2 : ℝ))/(N : ℝ) ∈ Icc (0 : ℝ) 1
  constructor
  · positivity
  · rw [div_le_iff₀ hNr,one_mul]
    have hk : ((k i : ℕ) : ℝ)+1 ≤ (N : ℝ) := by exact_mod_cast (k i).isLt
    linarith

theorem actual_centered_grid_in_cube (d N : ℕ) (hN : 0 < N) :
    ∀ z ∈ centeredGrid d N,z ∈ unitCube d := by
  classical
  intro z hz
  obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hz
  exact actual_centered_point_in_cube d N hN k

theorem actual_centered_half_diagonal (d N : ℕ) :
    (radius d N)^2=(d : ℝ)*(1/(2*(N : ℝ)))^2 := by
  rw [radius,div_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
  ring

theorem actual_centered_grid_covers (d N : ℕ) (hN : 0 < N) :
    IsFiniteNet (unitCube d) (centeredGrid d N) (radius d N) := by
  classical
  refine ⟨actual_centered_grid_in_cube d N hN,?_⟩
  intro x hx
  have hc : ∀ i : Fin d,∃ k : Fin N,|x i-((k : ℕ)+(1/2 : ℝ))/(N : ℝ)|≤1/(2*(N : ℝ)) :=
    fun i=>centered_coordinate_cover N hN (x i) (hx i)
  choose k hk using hc
  refine ⟨center d N k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,?_⟩
  have hs : dist x (center d N k)^2≤(d : ℝ)*(1/(2*(N : ℝ)))^2 := by
    rw [EuclideanSpace.dist_sq_eq]
    calc
      _ ≤ ∑ _i : Fin d,(1/(2*(N : ℝ)))^2 := by
        apply Finset.sum_le_sum
        intro i _
        have hi : dist (x i) (center d N k i)≤1/(2*(N : ℝ)) := by
          simpa only [center,PiLp.toLp_apply,Real.dist_eq] using hk i
        exact pow_le_pow_left₀ dist_nonneg hi 2
      _ = _ := by simp
  have hr:=actual_centered_half_diagonal d N
  have hp : 0≤radius d N := by unfold radius;positivity
  nlinarith [dist_nonneg (x:=x) (y:=center d N k)]

theorem actual_ceiling_grid_radius (d : ℕ) (hd : 0<d) (τ : ℝ) (hτ : 0<τ) :
    0<Nat.ceil (Real.sqrt d/(2*τ)) ∧
    radius d (Nat.ceil (Real.sqrt d/(2*τ)))≤τ := by
  have hdreal : (0 : ℝ)<d := by exact_mod_cast hd
  have hpos : 0<Real.sqrt d/(2*τ) := by positivity
  have hn : 0<Nat.ceil (Real.sqrt d/(2*τ)) := Nat.one_le_ceil_iff.mpr hpos
  have hnr : (0 : ℝ)<Nat.ceil (Real.sqrt d/(2*τ)) := by exact_mod_cast hn
  refine ⟨hn,?_⟩
  rw [radius,div_le_iff₀ (by positivity)]
  have hc:=Nat.le_ceil (Real.sqrt d/(2*τ))
  have hb:= (div_le_iff₀ (by positivity : 0<2*τ)).mp hc
  nlinarith

theorem actual_ceiling_cube_net_and_count (d : ℕ) (τ : ℝ) (hτ : 0<τ) :
    ∃ Z : Finset (EuclideanSpace ℝ (Fin d)), IsFiniteNet (unitCube d) Z τ ∧
      Z.card ≤ Nat.ceil (Real.sqrt d/(2*τ))^d := by
  classical
  by_cases hd : d=0
  · subst d
    refine ⟨{0},?_,by simp⟩
    constructor
    · intro z hz
      simp only [Finset.mem_singleton] at hz
      subst z
      intro i
      exact Fin.elim0 i
    · intro x hx
      refine ⟨0,Finset.mem_singleton_self _,?_⟩
      have he : x=0 := Subsingleton.elim _ _
      simpa [he] using hτ.le
  · have hc:=actual_ceiling_grid_radius d (by omega) τ hτ
    let N:=Nat.ceil (Real.sqrt d/(2*τ))
    refine ⟨centeredGrid d N,?_,?_⟩
    · refine ⟨(actual_centered_grid_covers d N hc.1).1,?_⟩
      intro x hx
      obtain ⟨z,hz,hr⟩:=(actual_centered_grid_covers d N hc.1).2 x hx
      exact ⟨z,hz,hr.trans hc.2⟩
    · rw [actual_centered_grid_cardinality d N hc.1]

theorem actual_covering_number_exists_and_obeys_source_bound (d : ℕ) (τ : ℝ) (hτ : 0<τ) :
    ∃ M : ℕ, IsLeast {n : ℕ | ∃ Z : Finset (EuclideanSpace ℝ (Fin d)),
      IsFiniteNet (unitCube d) Z τ ∧ Z.card=n} M ∧ M≤Nat.ceil (Real.sqrt d/(2*τ))^d := by
  classical
  obtain ⟨Z,hZ,hcount⟩:=actual_ceiling_cube_net_and_count d τ hτ
  have he : ∃ n : ℕ,∃ W : Finset (EuclideanSpace ℝ (Fin d)),IsFiniteNet (unitCube d) W τ ∧ W.card=n :=
    ⟨Z.card,Z,hZ,rfl⟩
  refine ⟨Nat.find he,⟨Nat.find_spec he,?_⟩,?_⟩
  · intro n hn
    exact Nat.find_min' he hn
  · exact (Nat.find_min' he ⟨Z,hZ,rfl⟩).trans hcount

theorem actual_source_two_dimensional_ceiling : Nat.ceil (Real.sqrt 2/(2*(1/10 : ℝ)))=8 := by
  rw [Nat.ceil_eq_iff (by norm_num : (8 : ℕ)≠0)]
  norm_num
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  have hn:=Real.sqrt_nonneg 2
  constructor <;> nlinarith

theorem actual_source_ten_dimensional_ceiling : Nat.ceil (Real.sqrt 10/(2*(1/10 : ℝ)))=16 := by
  rw [Nat.ceil_eq_iff (by norm_num : (16 : ℕ)≠0)]
  norm_num
  have hs:=Real.sq_sqrt (by norm_num : (0 : ℝ)≤10)
  have hn:=Real.sqrt_nonneg 10
  constructor <;> nlinarith

theorem actual_source_centered_counts_and_rounded_trillion :
    Nat.ceil (Real.sqrt 2/(2*(1/10 : ℝ)))^2=64 ∧
    Nat.ceil (Real.sqrt 10/(2*(1/10 : ℝ)))^10=1099511627776 ∧
    (1050000000000 : ℝ)<(16 : ℕ)^10 ∧ ((16 : ℕ)^10 : ℝ)<1150000000000 := by
  rw [actual_source_two_dimensional_ceiling,actual_source_ten_dimensional_ceiling]
  norm_num

theorem actual_generic_net_Lipschitz_margin {E : Type*} [PseudoMetricSpace E]
    (X : Set E) (Z : Finset E) (L : ℝ≥0) (τ : ℝ) (f : E→ℝ)
    (hf : LipschitzOnWith L f X) (hnet : IsFiniteNet X Z τ)
    (hmargin : ∀ z∈Z,(L : ℝ)*τ≤f z) : ∀ x∈X,0≤f x := by
  intro x hx
  obtain ⟨z,hz,hd⟩:=hnet.2 x hx
  have hl:=hf.dist_le_mul z (hnet.1 z hz) x hx
  rw [Real.dist_eq] at hl
  have hb:=le_abs_self (f z-f x)
  have hd' : dist z x≤τ := by simpa [dist_comm] using hd
  have hm:=mul_le_mul_of_nonneg_left hd' L.coe_nonneg
  have hv:=hmargin z hz
  linarith

end SafeLearning.CompleteFoundationsCenteredCubeNetsWhole30
