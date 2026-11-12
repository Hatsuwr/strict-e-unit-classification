import FiberTensorChart
import AlgebraicPoint
import PointedTorsor
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! The actual algebraic fiber at a k-valued base point. No domain,
connectedness, or identification with numerical values is assumed. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B R H : Type*} [Field k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k] [Algebra k H]

/-- The genuine base-changed coaction, constructed from the base-changed chart. -/
def algebraicFiberCoaction (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    (k ⊗[B] R) →ₐ[k] (k ⊗[B] R) ⊗[k] H :=
  inverseMultiplicationCoaction (fiberMultiplicationChart (A:=k) e)

theorem algebraicFiberCanonical_bijective
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    Function.Bijective (torsorCanonical (algebraicFiberCoaction e)) := by
  exact relativeCandidateCanonical_bijective (fiberMultiplicationChart (A:=k) e)

theorem algebraicFiber_finiteType [Algebra.FiniteType B R] :
    Algebra.FiniteType k (k ⊗[B] R) := inferInstance

theorem algebraicFiber_nontrivial [Module.FaithfullyFlat B R] :
    Nontrivial (k ⊗[B] R) := inferInstance

/-- The algebraic point follows from faithful flatness, finite type and
algebraic closedness, rather than being assumed. -/
theorem algebraicFiber_has_point [IsAlgClosed k] [Algebra.FiniteType B R]
    [Module.FaithfullyFlat B R] : Nonempty ((k ⊗[B] R) →ₐ[k] k) :=
  nonempty_algebraic_point

/-- An actual algebraic trivialization of the fiber, not a numerical evaluation map. -/
def algebraicFiberTrivialization [IsAlgClosed k] [Algebra.FiniteType B R]
    [Module.FaithfullyFlat B R]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) : (k ⊗[B] R) ≃ₐ[k] H :=
  pointedTorsorEquiv (algebraicFiberCoaction e)
    (Classical.choice (algebraicFiber_has_point (k:=k) (B:=B) (R:=R)))
    (algebraicFiberCanonical_bijective e)

end StrictEUnit
#print axioms StrictEUnit.algebraicFiberCoaction
#print axioms StrictEUnit.algebraicFiberCanonical_bijective
#print axioms StrictEUnit.algebraicFiber_finiteType
#print axioms StrictEUnit.algebraicFiber_nontrivial
#print axioms StrictEUnit.algebraicFiber_has_point
#print axioms StrictEUnit.algebraicFiberTrivialization
