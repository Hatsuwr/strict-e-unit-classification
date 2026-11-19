import Stage20ArithmeticFrameLifting
import Stage17ArithmeticFrameODE
import StrictETaylorRealization

/-! Transfer the explicit analytic Beukers input to the genuine ramified Taylor
frame. The polynomial identity is proved in the actual arithmetic entire ring
before applying its Taylor homomorphism. No evaluation on arbitrary formal
Laurent series is used. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- Polynomial substitution commutes with an actual algebra homomorphism. -/
theorem stage23_map_polynomial_mv_eval
    {k A C ι : Type*} [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] (φ : A →ₐ[k] C) (f : ι → A)
    (x : A) (Q : Polynomial (MvPolynomial ι k)) :
    φ (Polynomial.eval₂ (MvPolynomial.aeval f).toRingHom x Q) =
      Polynomial.eval₂ (MvPolynomial.aeval (fun i => φ (f i))).toRingHom (φ x) Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial j a =>
    simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
    congr 1
    exact MvPolynomial.comp_aeval_apply f φ a

/-- A pointwise global polynomial identity is an equality of actual arithmetic
entire functions, not a formal relation hypothesis. -/
theorem stage23_actual_polynomial_identity (k : Subfield ℂ) {ι : Type*}
    (f : ι → subfieldEntireFunctionAlgebra k)
    (Q : Polynomial (MvPolynomial ι k))
    (hQ : ∀ z : ℂ, Polynomial.eval₂
      (MvPolynomial.eval₂Hom k.subtype (fun i => (f i).val.val z)) z Q = 0) :
    Polynomial.eval₂ (MvPolynomial.aeval f).toRingHom (subfieldEntireCoordinate k) Q = 0 := by
  letI : CommRing entireFunctionAlgebra := Subalgebra.toCommRing entireFunctionAlgebra
  letI : CommRing (subfieldEntireFunctionAlgebra k) :=
    Subalgebra.toCommRing (subfieldEntireFunctionAlgebra k)
  apply Subtype.ext
  apply Subtype.ext
  funext z
  have h := stage23_map_polynomial_mv_eval
    (stage14_subfieldEntireEvaluation k z) f (subfieldEntireCoordinate k) Q
  exact h.trans (hQ z)

/-- Exact transfer to the genuine ramified formal frame, with t^N substituted
for the original coordinate. -/
theorem stage23_ramified_formal_polynomial_identity (k : Subfield ℂ)
    {ι : Type*} (N : ℕ) (hN : N ≠ 0)
    (f : ι → subfieldEntireFunctionAlgebra k)
    (Q : Polynomial (MvPolynomial ι k))
    (hQ : ∀ z : ℂ, Polynomial.eval₂
      (MvPolynomial.eval₂Hom k.subtype (fun i => (f i).val.val z)) z Q = 0) :
    Polynomial.eval₂
      (MvPolynomial.aeval (fun i => stage17_ramifiedEntireFormalAlgHom k N hN (f i))).toRingHom
      (formalBaseEmbedding (Polynomial.C (LaurentPolynomial.T 1)) ^ N) Q = 0 := by
  letI : CommRing entireFunctionAlgebra := Subalgebra.toCommRing entireFunctionAlgebra
  letI : CommRing (subfieldEntireFunctionAlgebra k) :=
    Subalgebra.toCommRing (subfieldEntireFunctionAlgebra k)
  have h := congrArg (stage17_ramifiedEntireFormalAlgHom k N hN)
    (stage23_actual_polynomial_identity k f Q hQ)
  rw [map_zero] at h
  have hc := stage23_map_polynomial_mv_eval (stage17_ramifiedEntireFormalAlgHom k N hN)
    f (subfieldEntireCoordinate k) Q
  have he := hc.symm.trans h
  have hx : stage17_ramifiedEntireFormalAlgHom k N hN (subfieldEntireCoordinate k) =
      formalBaseEmbedding (Polynomial.C (LaurentPolynomial.T 1)) ^ N := by
    rw [stage17_ramifiedEntireFormalAlgHom, AlgHom.comp_apply,
      stage17_arithmeticPowerPullback_coordinate, map_pow,
      stage17_entireFormalAlgHom_apply, stage17_entireLaurent_coordinate,
      formalBaseEmbedding_C]
    congr 2
    exact (laurentPolynomialToSeries_single 1 1).symm
  exact hx ▸ he

/-- The actual strict-E frame, equipped with its proved arithmetic Taylor
membership. No new frame existence premise is introduced. -/
def stage23_arithmeticFrame {n : Type*}
    (F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val) :
    Matrix n n (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :=
  fun i j => strictEFunctionTaylorRealization (F i j).val (hstrict i j)

/-- The unproved published lifting premise yields exact polynomial lifts on
this particular actual ramified formal frame. The final kernel is not assumed. -/
theorem stage23_arithmeticFrame_formal_polynomial_lifts
    (hBeukers : StrictELaurentRelationLifting)
    {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial AlgebraicComplex))
    (M : Matrix n n AlgebraicComplex) (F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z : ℂˣ, ∀ i j, (z : ℂ) * deriv (F i j).val (z : ℂ) =
      (∑ k, arithmeticLaurentEvaluation z (B i k) * (F k j).val (z : ℂ)) -
        ∑ k, (F i k).val (z : ℂ) * (M k j : ℂ))
    (P : MvPolynomial (n × n) (algebraicClosure ℚ ℂ).toSubfield)
    (hP : MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
      (fun ij => (F ij.1 ij.2).val 1) P = 0) :
    ∃ Q : Polynomial (MvPolynomial (n × n) (algebraicClosure ℚ ℂ).toSubfield),
      Polynomial.eval₂
        (MvPolynomial.aeval (R := (algebraicClosure ℚ ℂ).toSubfield) (fun ij => stage17_formalFrame
          (algebraicClosure ℚ ℂ).toSubfield N hN (stage23_arithmeticFrame F hstrict)
            ij.1 ij.2)).toRingHom
        (formalBaseEmbedding (Polynomial.C (LaurentPolynomial.T 1)) ^ N) Q = 0 ∧
      Q.eval 1 = P := by
  obtain ⟨Q, hQ, hQP⟩ :=
    arithmeticEulerFrame_exact_polynomial_lifts hBeukers B M F hstrict hF P hP
  refine ⟨Q, ?_, hQP⟩
  have hQ' : ∀ z : ℂ, Polynomial.eval₂
      (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).toSubfield.subtype
        (fun ij : n × n => (stage23_arithmeticFrame F hstrict ij.1 ij.2).val.val z)) z Q = 0 := hQ
  have h := stage23_ramified_formal_polynomial_identity (algebraicClosure ℚ ℂ).toSubfield
    N hN (fun ij : n × n => stage23_arithmeticFrame F hstrict ij.1 ij.2) Q hQ'
  exact h

/-- Direct arithmetic-frame form of the same lift, matching the actual frame
used by the formal system and the common-frame availability input. -/
theorem stage23_arithmeticEulerFrame_formal_polynomial_lifts
    (hBeukers : StrictELaurentRelationLifting)
    {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial (algebraicClosure ℚ ℂ).toSubfield))
    (M : Matrix n n (algebraicClosure ℚ ℂ).toSubfield)
    (F : Matrix n n (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield))
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)
    (hF : Stage17ActualEulerFrameRelation (algebraicClosure ℚ ℂ).toSubfield B M F)
    (P : MvPolynomial (n × n) (algebraicClosure ℚ ℂ).toSubfield)
    (hP : MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).toSubfield.subtype
      (fun ij => (F ij.1 ij.2).val.val 1) P = 0) :
    ∃ Q : Polynomial (MvPolynomial (n × n) (algebraicClosure ℚ ℂ).toSubfield),
      Polynomial.eval₂
        (MvPolynomial.aeval (R := (algebraicClosure ℚ ℂ).toSubfield)
          (fun ij : n × n => stage17_formalFrame
            (algebraicClosure ℚ ℂ).toSubfield N hN F ij.1 ij.2)).toRingHom
        (formalBaseEmbedding (Polynomial.C (LaurentPolynomial.T 1)) ^ N) Q = 0 ∧
      Q.eval 1 = P := by
  obtain ⟨Q, hQ, hQP⟩ := arithmeticEulerFrame_exact_polynomial_lifts
    hBeukers B M (fun i j => (F i j).val) hstrict hF P hP
  refine ⟨Q, ?_, hQP⟩
  have hQ' : ∀ z : ℂ, Polynomial.eval₂
      (MvPolynomial.eval₂Hom (algebraicClosure ℚ ℂ).toSubfield.subtype
        (fun ij : n × n => (F ij.1 ij.2).val.val z)) z Q = 0 := hQ
  exact stage23_ramified_formal_polynomial_identity (algebraicClosure ℚ ℂ).toSubfield
    N hN (fun ij : n × n => F ij.1 ij.2) Q hQ'

end StrictEUnit
