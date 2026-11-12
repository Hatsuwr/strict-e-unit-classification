import LaurentLogBasePointKernel
import LaurentLogPolynomialFiber
import LocalizedRelationFiber
import AlgebraicFiberQuotient

/-! Conditional algebraic consequence of genuine Beukers polynomial lifts.
The basepoint kernel, generator reduction, determinant localization and whole
fiber integrality are proved; existence of analytic evaluation and of the
polynomial lifts remains explicit. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k R L : Type*} [Field k] [CommRing R] [CommRing L]
  [Algebra k R] [Algebra (LaurentLogBase k) R] [IsScalarTower k (LaurentLogBase k) R]
  [Algebra k L]
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower

def manuscriptParameterUnit : Rˣ :=
  Units.map (algebraMap (LaurentLogBase k) R).toMonoidHom (laurentLogBaseT k)

def manuscriptLogParameter : R := algebraMap (LaurentLogBase k) R Polynomial.X

omit [Algebra k R] [IsScalarTower k (LaurentLogBase k) R] in
theorem extended_basePoint_kernel :
    Ideal.map (algebraMap (LaurentLogBase k) R)
      (RingHom.ker (algebraMap (LaurentLogBase k) k)) =
      laurentLogFiberIdeal (manuscriptParameterUnit (k:=k) (R:=R))
        (manuscriptLogParameter (k:=k) (R:=R)) := by
  change Ideal.map _ (RingHom.ker (laurentLogBasePoint k).toRingHom) = _
  rw [laurentLogBasePoint_kernel]
  simp [laurentLogBasePointIdeal, laurentLogFiberIdeal, Ideal.map_span,
    manuscriptParameterUnit, manuscriptLogParameter, Set.image_insert_eq, Set.image_singleton]

variable {ι : Type*}
/-- Exact kernel from the explicit polynomial-lifting input at t=1,ell=0. -/
theorem manuscript_exact_kernel_of_polynomial_lifts
    (ev : R →ₐ[k] L) (F : ι → R) (N : ℕ)
    (hgen : Algebra.adjoin k (Set.range F ∪ Set.range
      (laurentLogFiberParameters (manuscriptParameterUnit (k:=k) (R:=R))
        (manuscriptLogParameter (k:=k) (R:=R)))) = ⊤)
    (ht : ev (manuscriptParameterUnit (k:=k) (R:=R) : R) = 1)
    (hl : ev (manuscriptLogParameter (k:=k) (R:=R)) = 0)
    (hlift : ∀ P : MvPolynomial ι k, ev (MvPolynomial.aeval F P) = 0 →
      ∃ Q : Polynomial (MvPolynomial ι k),
        Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom
          ((manuscriptParameterUnit (k:=k) (R:=R) : R)^N) Q = 0 ∧ Q.eval 1 = P) :
    RingHom.ker ev.toRingHom = Ideal.map (algebraMap (LaurentLogBase k) R)
      (RingHom.ker (algebraMap (LaurentLogBase k) k)) := by
  rw [extended_basePoint_kernel]
  exact laurentLogFiber_kernel_of_polynomial_lifts ev _ _ F N hgen ht hl hlift

/-- The actual tensor fiber is a domain, not merely its numerical image. -/
theorem manuscript_fiber_isDomain_of_polynomial_lifts [IsDomain L]
    (ev : R →ₐ[k] L) (F : ι → R) (N : ℕ)
    (hgen : Algebra.adjoin k (Set.range F ∪ Set.range
      (laurentLogFiberParameters (manuscriptParameterUnit (k:=k) (R:=R))
        (manuscriptLogParameter (k:=k) (R:=R)))) = ⊤)
    (ht : ev (manuscriptParameterUnit (k:=k) (R:=R) : R) = 1)
    (hl : ev (manuscriptLogParameter (k:=k) (R:=R)) = 0)
    (hlift : ∀ P : MvPolynomial ι k, ev (MvPolynomial.aeval F P) = 0 →
      ∃ Q : Polynomial (MvPolynomial ι k),
        Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom
          ((manuscriptParameterUnit (k:=k) (R:=R) : R)^N) Q = 0 ∧ Q.eval 1 = P) :
    IsDomain (k ⊗[LaurentLogBase k] R) :=
  algebraicFiber_isDomain_of_exact_evaluation ev.toRingHom
    (manuscript_exact_kernel_of_polynomial_lifts ev F N hgen ht hl hlift)
end StrictEUnit
#print axioms StrictEUnit.manuscriptParameterUnit
#print axioms StrictEUnit.manuscriptLogParameter
#print axioms StrictEUnit.extended_basePoint_kernel
#print axioms StrictEUnit.manuscript_exact_kernel_of_polynomial_lifts
#print axioms StrictEUnit.manuscript_fiber_isDomain_of_polynomial_lifts
