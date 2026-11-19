import V5HopfQuotientCharacter135
import V5GenericOwnFixed123
import V5WideMixedConstantDomain
noncomputable section
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option maxRecDepth 1800
set_option synthInstance.maxHeartbeats 45000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
namespace StrictEUnit
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {r : ℕ} (f : Fin r → entireFunctionAlgebra)
  (A : Matrix (Fin r) (Fin r) V5LaurentBase)
  (hf : ∀ i, V5IsBroadEFunction (f i).val)
  (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
    ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
/-- Actual mixed units have normalized grouplike characters on the very
identity quotient used by the actual component cover. -/
def v5ActualQuotientCharacter135 := by
  letI := v5WideOwnHopfAlgebra A
  letI : Algebra.FiniteType AlgebraicComplex (V5WideOwnConstants A) :=
    v5WideOwnConstants_finiteType A
  letI : IsDomain (V5WideActualMixedConstants104 f A hA) :=
    v5WideMixedConstantDomain f A hf hA
  let spec := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).1
  let uniq := (Classical.choose_spec (v5GenericOwnUniqueIdentity123 A)).2
  exact v5HopfQuotientCharacter135 (v5WideMixedAction f A hA)
    (v5GenericOwnIdentity123 A) spec.1 spec.2
    (fun P hP hPε => uniq P ⟨hP, hPε⟩)
    (v5WideMixedAction_counit f A hA) (v5WideMixedAction_coassoc f A hA)
/-- The original reciprocal fiber unit gives a character on the cover's
identity quotient, with no transport from the older selected ideal. -/
def v5ActualReciprocalCharacter135 (i j : Fin r)
    (hij : (f i).val 1 * (f j).val 1 = 1) :=
  (v5ActualQuotientCharacter135 f A hf hA)
    (v5WideMixedConstantUnit f A hf hA i j hij)
end StrictEUnit
#print axioms StrictEUnit.v5ActualQuotientCharacter135
#print axioms StrictEUnit.v5ActualReciprocalCharacter135
