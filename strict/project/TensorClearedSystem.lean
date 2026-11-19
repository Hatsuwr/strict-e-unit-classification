import Stage35HomogeneousOrdinaryLifting
import Stage15StrictEDeterminantClassification
import DeterminantalIdealStability

/-!
A concrete tensor-word construction for the degree-one reduction.
No lifting theorem is proved or assumed in this file.
The product tuple has duplicate coordinates, deliberately: this avoids a
basis selection that could introduce singularities at the lifting point.
-/
noncomputable section
open scoped BigOperators Topology
namespace StrictEUnit

/-- Products indexed by words of a fixed length. -/
def tensorWordFunctions {ι κ : Type*} [Fintype κ]
    (f : ι → entireFunctionAlgebra) (w : κ → ι) : entireFunctionAlgebra :=
  ∏ k, f (w k)

@[simp] theorem tensorWordFunctions_apply {ι κ : Type*} [Fintype κ]
    (f : ι → entireFunctionAlgebra) (w : κ → ι) (z : ℂ) :
    (tensorWordFunctions f w).val z = ∏ k, (f (w k)).val z := by
  change (entireEvaluation z).toRingHom (∏ k, f (w k)) = _
  exact map_prod _ _ _

/-- Full strict-E closure, not merely closure of the analytic series. -/
theorem tensorWordFunctions_strict {ι κ : Type*} [Fintype κ]
    (f : ι → entireFunctionAlgebra) (hf : ∀ i, IsStrictEFunction (f i).val)
    (w : κ → ι) : IsStrictEFunction (tensorWordFunctions f w).val := by
  have he : (tensorWordFunctions f w).val = ∏ k, (f (w k)).val := by
    funext z
    simp only [tensorWordFunctions_apply, Finset.prod_apply]
  rw [he]
  exact strictEFunctionSubring.prod_mem (fun k _ => hf (w k))

/-- The tensor connection is a sum over single-coordinate transitions.
Every entry stays in the original polynomial coefficient ring. -/
def tensorWordMatrix {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    (B : Matrix ι ι R) : Matrix (κ → ι) (κ → ι) R := by
  classical
  exact fun w v => ∑ k, ∑ j, if v = Function.update w k j then B (w k) j else 0

/-- Evaluation of the explicit matrix action. Repeated transitions add. -/
theorem tensorWordMatrix_mul {ι κ R S : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (B : Matrix ι ι R) (g : (κ → ι) → S) (w : κ → ι) :
    ∑ v, φ (tensorWordMatrix B w v) * g v =
      ∑ k, ∑ j, φ (B (w k) j) * g (Function.update w k j) := by
  classical
  simp only [tensorWordMatrix, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp [apply_ite]
  first
  | rfl
  | apply congrArg (fun v : κ → ι => φ (B (w k) j) * g v)
    funext l
    by_cases hl : l = k <;> simp [Function.update_apply, hl]

/-- The derivative of a finite product, expressed in actual entire functions. -/
theorem tensorWordFunctions_deriv {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → entireFunctionAlgebra) (w : κ → ι) (z : ℂ) :
    deriv (tensorWordFunctions f w).val z =
      ∑ k, (∏ l ∈ Finset.univ.erase k, (f (w l)).val z) * deriv (f (w k)).val z := by
  classical
  have hsum (s : Finset κ) (F : κ → entireFunctionAlgebra) :
      (entireEvaluation z).toRingHom (∑ k ∈ s, F k) =
        ∑ k ∈ s, (entireEvaluation z).toRingHom (F k) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact RingHom.map_zero (entireEvaluation z).toRingHom
    | @insert k s hk ih =>
      rw [Finset.sum_insert hk,
        RingHom.map_add (entireEvaluation z).toRingHom (F k) (∑ l ∈ s, F l),
        ih, Finset.sum_insert hk]
  have hprod (s : Finset κ) (F : κ → entireFunctionAlgebra) :
      (entireEvaluation z).toRingHom (∏ k ∈ s, F k) =
        ∏ k ∈ s, (entireEvaluation z).toRingHom (F k) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact RingHom.map_one (entireEvaluation z).toRingHom
    | @insert k s hk ih =>
      rw [Finset.prod_insert hk,
        RingHom.map_mul (entireEvaluation z).toRingHom (F k) (∏ l ∈ s, F l),
        ih, Finset.prod_insert hk]
  change (entireEvaluation z).toRingHom
    (entireFunctionDerivation (∏ k, f (w k))) = _
  rw [derivation_finset_prod]
  rw [hsum Finset.univ (fun k : κ =>
    (∏ l ∈ Finset.univ.erase k, f (w l)) * entireFunctionDerivation (f (w k)))]
  apply Finset.sum_congr rfl
  intro k hk
  rw [RingHom.map_mul (entireEvaluation z).toRingHom
    (∏ l ∈ Finset.univ.erase k, f (w l)) (entireFunctionDerivation (f (w k))),
    hprod (Finset.univ.erase k) (fun l : κ => f (w l))]
  rfl

/-- Replacing one letter changes exactly one factor, with no division. -/
theorem tensorWordFunctions_update {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ι → entireFunctionAlgebra) (w : κ → ι) (k : κ) (j : ι) (z : ℂ) :
    (tensorWordFunctions f (Function.update w k j)).val z =
      (f j).val z * ∏ l ∈ Finset.univ.erase k, (f (w l)).val z := by
  classical
  rw [tensorWordFunctions_apply,
    ← Finset.mul_prod_erase Finset.univ (fun l => (f (Function.update w k j l)).val z)
      (Finset.mem_univ k)]
  simp only [Function.update_same]
  congr 1
  apply Finset.prod_congr rfl
  intro l hl
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]

/-- Tensor powers use the SAME clearing polynomial t, so no new pole is
introduced at 1. Holds even for empty types and for degree zero. -/
theorem tensorWordFunctions_clearedSystem {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (f : ι → entireFunctionAlgebra) (t : Polynomial AlgebraicComplex)
    (B : Matrix ι ι (Polynomial AlgebraicComplex)) (hs : Stage35ClearedSystem f t B) :
    Stage35ClearedSystem (tensorWordFunctions (κ := κ) f) t (tensorWordMatrix B) := by
  classical
  intro z w
  have hmatrix := tensorWordMatrix_mul
    (Polynomial.eval₂RingHom (algebraicClosure ℚ ℂ).val.toRingHom z) B
    (fun v : κ → ι => (tensorWordFunctions f v).val z) w
  change (∑ v : κ → ι,
      (tensorWordMatrix B w v).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
        (tensorWordFunctions f v).val z) =
    ∑ k, ∑ j, (B (w k) j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      (tensorWordFunctions f (Function.update w k j)).val z at hmatrix
  rw [tensorWordFunctions_deriv, Finset.mul_sum, hmatrix]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, mul_comm (t.eval₂ _ z), mul_assoc, hs z (w k), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [tensorWordFunctions_update]
  ring

/-- Word monomials used to substitute a linear relation back into the
original function variables. -/
def tensorWordMonomial {ι R : Type*} [CommSemiring R] (D : ℕ)
    (w : Fin D → ι) : MvPolynomial ι R := ∏ k, MvPolynomial.X (w k)

theorem tensorWordMonomial_homogeneous {ι R : Type*} [CommSemiring R]
    (D : ℕ) (w : Fin D → ι) : (tensorWordMonomial (R := R) D w).IsHomogeneous D := by
  simpa [tensorWordMonomial] using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun k => MvPolynomial.X (R := R) (w k)) (fun _ => 1)
      (fun k _ => MvPolynomial.isHomogeneous_X R (w k))

/-- Substitution from the redundant degree-D variables into the old ones. -/
def tensorWordSubstitution {ι R : Type*} [CommSemiring R] (D : ℕ) :
    MvPolynomial (Fin D → ι) R →+* MvPolynomial ι R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (tensorWordMonomial D)

theorem tensorWordSubstitution_homogeneous {ι R : Type*} [CommSemiring R]
    (D : ℕ) (L : MvPolynomial (Fin D → ι) R) (hL : L.IsHomogeneous 1) :
    (tensorWordSubstitution D L).IsHomogeneous D := by
  simpa only [mul_one] using hL.eval₂ MvPolynomial.C (tensorWordMonomial D)
    (fun a => MvPolynomial.isHomogeneous_C _ a) (tensorWordMonomial_homogeneous D)

theorem tensorWordSubstitution_eval {ι R S : Type*} [CommSemiring R] [CommSemiring S]
    (D : ℕ) (φ : R →+* S) (f : ι → S) (L : MvPolynomial (Fin D → ι) R) :
    MvPolynomial.eval₂ φ f (tensorWordSubstitution D L) =
      MvPolynomial.eval₂ φ (fun w => ∏ k, f (w k)) L := by
  have h : (MvPolynomial.eval₂Hom φ f).comp (tensorWordSubstitution D) =
      MvPolynomial.eval₂Hom φ (fun w => ∏ k, f (w k)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [tensorWordSubstitution]
    · intro w
      simp [tensorWordSubstitution, tensorWordMonomial]
  exact DFunLike.congr_fun h L

end StrictEUnit
