import Mathlib
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace SafeLearning.CompleteFoundationsMatrixConjugate
open Set
open scoped BigOperators Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

def sourceQuadratic (Q : Matrix n n ℝ) (x : n→ℝ) : ℝ := (x ⬝ᵥ (Q *ᵥ x))/2
def pairingObjective (Q : Matrix n n ℝ) (y x : n→ℝ) : ℝ := y ⬝ᵥ x-sourceQuadratic Q x
def sourceConjugate (Q : Matrix n n ℝ) (y : n→ℝ) : EReal :=
  sSup (range (fun x : n→ℝ => (pairingObjective Q y x : EReal)))
def optimizer (Q : Matrix n n ℝ) (y : n→ℝ) : n→ℝ := Q⁻¹ *ᵥ y

theorem actual_inverse_stationary_solution (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y : n→ℝ) :
    Q *ᵥ optimizer Q y=y := by
  letI := hQ.isUnit.invertible
  rw [optimizer,Matrix.mulVec_mulVec,Matrix.mul_inv_of_invertible,Matrix.one_mulVec]

theorem actual_symmetric_cross_pairing (Q : Matrix n n ℝ) (hQ : Q.IsHermitian) (x z : n→ℝ) :
    x ⬝ᵥ (Q *ᵥ z)=z ⬝ᵥ (Q *ᵥ x) := by
  simpa only [star_trivial,Pi.star_apply] using hQ.star_dotProduct_mulVec_comm x z

theorem actual_completed_square_identity (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y x : n→ℝ) :
    pairingObjective Q y x=sourceQuadratic Q⁻¹ y-sourceQuadratic Q (x-optimizer Q y) := by
  have hc:=actual_symmetric_cross_pairing Q hQ.isHermitian x (optimizer Q y)
  have hi:=actual_inverse_stationary_solution Q hQ y
  have ho : sourceQuadratic Q (optimizer Q y)=sourceQuadratic Q⁻¹ y := by
    unfold sourceQuadratic
    rw [hi]
    simp only [optimizer]
    rw [dotProduct_comm]
  rw [hi] at hc
  unfold pairingObjective sourceQuadratic
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub]
  rw [hi]
  have ho' : optimizer Q y ⬝ᵥ y / 2=y ⬝ᵥ (Q⁻¹ *ᵥ y) / 2 := by
    simpa only [sourceQuadratic,hi] using ho
  rw [←dotProduct_comm y x]
  rw [dotProduct_comm x y] at hc
  linarith [ho',hc]

theorem actual_global_objective_upper_and_equality_iff (Q : Matrix n n ℝ)
    (hQ : Q.PosDef) (y x : n→ℝ) :
    pairingObjective Q y x ≤ sourceQuadratic Q⁻¹ y ∧
    (pairingObjective Q y x=sourceQuadratic Q⁻¹ y ↔ x=optimizer Q y) := by
  rw [actual_completed_square_identity Q hQ]
  have hp : 0 ≤ sourceQuadratic Q (x-optimizer Q y) := by
    have h:=hQ.posSemidef.dotProduct_mulVec_nonneg (x-optimizer Q y)
    simpa only [sourceQuadratic,Pi.star_apply,star_trivial] using div_nonneg h (by norm_num : (0:ℝ)≤2)
  refine ⟨by linarith,?_⟩
  constructor
  · intro he
    by_contra hn
    have hx : x-optimizer Q y≠0 := sub_ne_zero.mpr hn
    have hpos : 0 < sourceQuadratic Q (x-optimizer Q y) := by
      have h:=hQ.dotProduct_mulVec_pos hx
      simpa only [sourceQuadratic,Pi.star_apply,star_trivial] using div_pos h (by norm_num : (0:ℝ)<2)
    linarith
  · intro he
    rw [he,sub_self]
    simp [sourceQuadratic]

theorem actual_supremum_and_unique_attainer (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y : n→ℝ) :
    IsLUB (range (pairingObjective Q y)) (sourceQuadratic Q⁻¹ y) ∧
    ∃! x : n→ℝ,pairingObjective Q y x=sourceQuadratic Q⁻¹ y := by
  refine ⟨⟨?_,?_⟩,optimizer Q y,?_,?_⟩
  · rintro z ⟨x,rfl⟩
    exact (actual_global_objective_upper_and_equality_iff Q hQ y x).1
  · intro upper hu
    have he:pairingObjective Q y (optimizer Q y)=sourceQuadratic Q⁻¹ y :=
      (actual_global_objective_upper_and_equality_iff Q hQ y (optimizer Q y)).2.mpr rfl
    simpa [he] using hu (mem_range_self (optimizer Q y))
  · exact (actual_global_objective_upper_and_equality_iff Q hQ y (optimizer Q y)).2.mpr rfl
  · intro x hx
    exact (actual_global_objective_upper_and_equality_iff Q hQ y x).2.mp hx

theorem actual_extended_real_source_conjugate (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y : n→ℝ) :
    sourceConjugate Q y=(sourceQuadratic Q⁻¹ y : EReal) := by
  apply le_antisymm
  · apply sSup_le
    rintro z ⟨x,rfl⟩
    exact EReal.coe_le_coe (actual_global_objective_upper_and_equality_iff Q hQ y x).1
  · have he:pairingObjective Q y (optimizer Q y)=sourceQuadratic Q⁻¹ y :=
      (actual_global_objective_upper_and_equality_iff Q hQ y (optimizer Q y)).2.mpr rfl
    exact le_sSup ⟨optimizer Q y,congrArg (fun r:ℝ=>(r:EReal)) he⟩

theorem actual_pairing_Jensen_gap_identity (Q : Matrix n n ℝ) (y x z : n→ℝ)
    (s t : ℝ) (hst : s+t=1) :
    pairingObjective Q y (s • x+t • z)-(s*pairingObjective Q y x+t*pairingObjective Q y z)=
      s*t*sourceQuadratic Q (x-z) := by
  unfold pairingObjective sourceQuadratic
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,Matrix.mulVec_smul,
    dotProduct_add,add_dotProduct,dotProduct_sub,sub_dotProduct,dotProduct_smul,
    smul_dotProduct,smul_eq_mul]
  have ht : t=1-s := by linarith
  rw [ht]
  ring

theorem actual_pairing_objective_is_concave (Q : Matrix n n ℝ) (hQ : Q.PosDef) (y : n→ℝ) :
    ConcaveOn ℝ univ (pairingObjective Q y) := by
  refine ⟨convex_univ,?_⟩
  intro x _ z _ s t hs ht hst
  have h:=hQ.posSemidef.dotProduct_mulVec_nonneg (x-z)
  have hp : 0 ≤ sourceQuadratic Q (x-z) := by
    simpa only [sourceQuadratic,Pi.star_apply,star_trivial] using div_nonneg h (by norm_num : (0:ℝ)≤2)
  have hm:=mul_nonneg (mul_nonneg hs ht) hp
  have he:=actual_pairing_Jensen_gap_identity Q y x z s t hst
  change s*pairingObjective Q y x+t*pairingObjective Q y z ≤ pairingObjective Q y (s • x+t • z)
  linarith

abbrev E (n : Type*) := EuclideanSpace ℝ n
def operator (Q : Matrix n n ℝ) : E n →L[ℝ] E n := Matrix.toEuclideanCLM (n:=n) (𝕜:=ℝ) Q
def euclideanQuadratic (Q : Matrix n n ℝ) (x : E n) : ℝ := inner ℝ x (operator Q x)/2

theorem actual_operator_coordinates (Q : Matrix n n ℝ) (x : E n) (i : n) :
    operator Q x i=(Q *ᵥ (x : n→ℝ)) i := by rfl

theorem actual_euclidean_quadratic_correspondence (Q : Matrix n n ℝ) (x : E n) :
    euclideanQuadratic Q x=sourceQuadratic Q (x : n→ℝ) := by
  simp only [euclideanQuadratic,sourceQuadratic,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,actual_operator_coordinates,dotProduct,mul_comm]

theorem actual_euclidean_symmetric_pairing (Q : Matrix n n ℝ) (hQ : Q.IsHermitian) (x z : E n) :
    inner ℝ x (operator Q z)=inner ℝ (operator Q x) z := by
  have h:=actual_symmetric_cross_pairing Q hQ (x : n→ℝ) (z : n→ℝ)
  simpa only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,actual_operator_coordinates,dotProduct,mul_comm] using h

theorem actual_quadratic_gradient (Q : Matrix n n ℝ) (hQ : Q.IsHermitian) (x : E n) :
    HasGradientAt (euclideanQuadratic Q) (operator Q x) x := by
  have hi : HasFDerivAt (fun z:E n=>z) (ContinuousLinearMap.id ℝ (E n)) x := hasFDerivAt_id x
  have ho := (operator Q).hasFDerivAt (x:=x)
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hi.inner ℝ ho).const_mul (1/2) using 1
  · funext z
    simp [euclideanQuadratic]
    ring
  · ext u
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,smul_eq_mul,
      fderivInnerCLM_apply,InnerProductSpace.toDual_apply_apply]
    rw [actual_euclidean_symmetric_pairing Q hQ x u,real_inner_comm u (operator Q x)]
    ring

def euclideanPairingObjective (Q : Matrix n n ℝ) (y x : E n) : ℝ :=
  inner ℝ y x-euclideanQuadratic Q x

theorem actual_pairing_objective_gradient (Q : Matrix n n ℝ) (hQ : Q.IsHermitian) (y x : E n) :
    HasGradientAt (euclideanPairingObjective Q y) (y-operator Q x) x := by
  have hl : HasGradientAt (fun z:E n=>inner ℝ y z) y x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (InnerProductSpace.toDual ℝ (E n) y).hasFDerivAt
  have hq := actual_quadratic_gradient Q hQ x
  rw [hasGradientAt_iff_hasFDerivAt] at hl hq ⊢
  convert hl.sub hq using 1
  · funext z;rfl
  · simp only [map_sub]
end SafeLearning.CompleteFoundationsMatrixConjugate
