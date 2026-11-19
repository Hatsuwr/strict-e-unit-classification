import Stage20TwoSidedVectorization
import PolynomialRelationFiber

/-! An explicit statement of the still-unproved exact relation-lifting input,
plus its application to the actual two-sided arithmetic frame. This hypothesis
is not an axiom, and the theorem below does not prove Beukers' theorem. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Actual Laurent evaluation of algebraic coefficients at a nonzero point. -/
def arithmeticLaurentEvaluation (z : ℂˣ) : LaurentPolynomial AlgebraicComplex →+* ℂ :=
  LaurentPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z

/-- Exact polynomial relation lifting for strict-E vectors in Laurent systems,
at the ordinary nonzero algebraic point 1. This is an explicit external
mathematical premise, not a theorem proved in this development. -/
def StrictELaurentRelationLifting : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex)),
    (∀ i, IsStrictEFunction (f i).val) →
    (∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ)) →
    ∀ P : MvPolynomial ι AlgebraicComplex,
      MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
        (fun i => (f i).val 1) P = 0 →
      ∃ Q : Polynomial (MvPolynomial ι AlgebraicComplex),
        (∀ z : ℂ, Polynomial.eval₂
          (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).val.toRingHom
            (fun i => (f i).val z)) z Q = 0) ∧ Q.eval 1 = P

/-- The actual vector coefficient matrix of the punctured Euler frame equation. -/
def arithmeticEulerFrameVectorMatrix {n : Type} [DecidableEq n]
    (B : Matrix n n (LaurentPolynomial AlgebraicComplex))
    (M : Matrix n n AlgebraicComplex) :
    Matrix (n × n) (n × n) (LaurentPolynomial AlgebraicComplex) :=
  twoSidedVectorMatrix (fun i j => B i j * LaurentPolynomial.T (-1))
    (fun i j => LaurentPolynomial.C (M i j) * LaurentPolynomial.T (-1))

/-- The Laurent first-order system is proved from the actual two-sided Euler
identity; it is not separately assumed in the relation-lifting application. -/
theorem arithmeticEulerFrame_vector_system {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n (LaurentPolynomial AlgebraicComplex))
    (M : Matrix n n AlgebraicComplex) (F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ z : ℂˣ, ∀ i j, (z : ℂ) * deriv (F i j).val (z : ℂ) =
      (∑ k, arithmeticLaurentEvaluation z (B i k) * (F k j).val (z : ℂ)) -
        ∑ k, (F i k).val (z : ℂ) * (M k j : ℂ)) :
    ∀ z : ℂˣ, ∀ ij : n × n, deriv (F ij.1 ij.2).val (z : ℂ) =
      ∑ kl : n × n, arithmeticLaurentEvaluation z
        (arithmeticEulerFrameVectorMatrix B M ij kl) * (F kl.1 kl.2).val (z : ℂ) := by
  intro z ij
  have hz : (z : ℂ) ≠ 0 := Units.ne_zero z
  have hT : arithmeticLaurentEvaluation z (LaurentPolynomial.T (-1)) = (z : ℂ)⁻¹ := by
    simpa only [arithmeticLaurentEvaluation, pow_one, Nat.cast_one, Units.val_inv_eq_inv_val] using
      LaurentPolynomial.eval₂_T_neg_n (algebraicClosure ℚ ℂ).val.toRingHom z 1
  simp only [arithmeticEulerFrameVectorMatrix, twoSidedVectorMatrix_map]
  have hv := twoSidedVectorMatrix_mulVec
    (Matrix.map (fun i j => B i j * LaurentPolynomial.T (-1)) (arithmeticLaurentEvaluation z))
    (Matrix.map (fun i j => LaurentPolynomial.C (M i j) * LaurentPolynomial.T (-1))
      (arithmeticLaurentEvaluation z)) (F.map (entireEvaluation (z : ℂ))) ij.1 ij.2
  change (∑ x, twoSidedVectorMatrix _ _ ij x * (F x.1 x.2).val (z : ℂ)) = _ at hv
  rw [hv]
  apply mul_left_cancel₀ hz
  rw [hF, mul_sub, Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (fun x y : ℂ => x - y)
  · apply Finset.sum_congr rfl
    intro k hk
    change arithmeticLaurentEvaluation z (B ij.1 k) * (F k ij.2).val (z : ℂ) =
      (z : ℂ) * (arithmeticLaurentEvaluation z (B ij.1 k * LaurentPolynomial.T (-1)) *
        (F k ij.2).val (z : ℂ))
    rw [map_mul, hT]
    field_simp
  · apply Finset.sum_congr rfl
    intro k hk
    change (F ij.1 k).val (z : ℂ) * (M k ij.2 : ℂ) =
      (z : ℂ) * ((F ij.1 k).val (z : ℂ) *
        arithmeticLaurentEvaluation z (LaurentPolynomial.C (M k ij.2) * LaurentPolynomial.T (-1)))
    rw [map_mul, hT]
    simp only [arithmeticLaurentEvaluation, LaurentPolynomial.eval₂_C]
    field_simp

/-- Conditional exact relation lifting for the actual arithmetic frame. The
only new arithmetic theorem premise is explicitly named hBeukers. -/
theorem arithmeticEulerFrame_exact_polynomial_lifts
    (hBeukers : StrictELaurentRelationLifting)
    {n : Type} [Fintype n] [DecidableEq n]
    (B : Matrix n n (LaurentPolynomial AlgebraicComplex))
    (M : Matrix n n AlgebraicComplex) (F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z : ℂˣ, ∀ i j, (z : ℂ) * deriv (F i j).val (z : ℂ) =
      (∑ k, arithmeticLaurentEvaluation z (B i k) * (F k j).val (z : ℂ)) -
        ∑ k, (F i k).val (z : ℂ) * (M k j : ℂ))
    (P : MvPolynomial (n × n) AlgebraicComplex)
    (hP : MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
      (fun ij => (F ij.1 ij.2).val 1) P = 0) :
    ∃ Q : Polynomial (MvPolynomial (n × n) AlgebraicComplex),
      (∀ z : ℂ, Polynomial.eval₂
        (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).val.toRingHom
          (fun ij => (F ij.1 ij.2).val z)) z Q = 0) ∧ Q.eval 1 = P :=
  hBeukers (n × n) (fun ij => F ij.1 ij.2)
    (arithmeticEulerFrameVectorMatrix B M) (fun ij => hstrict ij.1 ij.2)
      (arithmeticEulerFrame_vector_system B M F hF) P hP

end StrictEUnit
#print axioms StrictEUnit.arithmeticLaurentEvaluation
#print axioms StrictEUnit.StrictELaurentRelationLifting
#print axioms StrictEUnit.arithmeticEulerFrameVectorMatrix
#print axioms StrictEUnit.arithmeticEulerFrame_vector_system
#print axioms StrictEUnit.arithmeticEulerFrame_exact_polynomial_lifts
