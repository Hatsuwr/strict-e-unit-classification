import LaurentLogBase
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! The actual k-point t=1, ell=0 of the abstract manuscript base.
This is algebraic evaluation, not evaluation of an analytic logarithm. -/
noncomputable section
namespace StrictEUnit
variable (k : Type*) [Field k]

def laurentEvaluateOne : LaurentPolynomial k →ₐ[k] k :=
  AddMonoidAlgebra.lift k ℤ k (1 : Multiplicative ℤ →* k)

@[simp] theorem laurentEvaluateOne_single (n:ℤ) (a:k) :
    laurentEvaluateOne k (AddMonoidAlgebra.single n a) = a := by
  rw [laurentEvaluateOne, AddMonoidAlgebra.lift_single]
  simp

def laurentLogBasePoint : LaurentLogBase k →ₐ[k] k :=
  Polynomial.aevalTower (laurentEvaluateOne k) 0

@[simp] theorem laurentLogBasePoint_C (p : LaurentPolynomial k) :
    laurentLogBasePoint k (Polynomial.C p) = laurentEvaluateOne k p := by
  simp [laurentLogBasePoint, Polynomial.aevalTower]

@[simp] theorem laurentLogBasePoint_X :
    laurentLogBasePoint k Polynomial.X = 0 := by
  simp [laurentLogBasePoint, Polynomial.aevalTower]

@[simp] theorem laurentLogBasePoint_monomial (n:ℤ) (a:k) :
    laurentLogBasePoint k (Polynomial.C (AddMonoidAlgebra.single n a)) = a := by
  rw [laurentLogBasePoint_C, laurentEvaluateOne_single]

def laurentLogPointAlgebra : Algebra (LaurentLogBase k) k :=
  (laurentLogBasePoint k).toRingHom.toAlgebra

def laurentLogPointTower := IsScalarTower.of_algHom (laurentLogBasePoint k)

#print axioms laurentLogPointAlgebra
#print axioms laurentLogPointTower
#print axioms laurentEvaluateOne
#print axioms laurentEvaluateOne_single
#print axioms laurentLogBasePoint
#print axioms laurentLogBasePoint_C
#print axioms laurentLogBasePoint_X
#print axioms laurentLogBasePoint_monomial
end StrictEUnit
