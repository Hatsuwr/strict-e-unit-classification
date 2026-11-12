import AlgebraicPointAvoidance
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic

/-! Tensor products of domains over an algebraically closed field.
Only the second factor is required to be of finite type. Nonzero tensors are
separated simultaneously by an actual algebraic point of that factor. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

def tensorPointEvaluation (p : B →ₐ[k] k) : A ⊗[k] B →ₐ[k] A :=
  Algebra.TensorProduct.productMap (AlgHom.id k A) ((Algebra.ofId k A).comp p)

@[simp] theorem tensorPointEvaluation_tmul (p : B →ₐ[k] k) (a : A) (b : B) :
    tensorPointEvaluation (A := A) p (a ⊗ₜ[k] b) = p b • a := by
  change a * algebraMap k A (p b) = p b • a
  rw [Algebra.smul_def, mul_comm]

theorem tensorPointEvaluation_coordinate {ι : Type*} [DecidableEq ι] (e : Basis ι k A)
    (p : B →ₐ[k] k) (x : A ⊗[k] B) (i : ι) :
    e.repr (tensorPointEvaluation p x) i =
      p (TensorProduct.equivFinsuppOfBasisLeft e x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply, mul_comm]
  | add x y hx hy => simp [hx, hy]

variable [IsAlgClosed k] [IsDomain A] [IsDomain B] [Algebra.FiniteType k B]

omit [IsDomain A] in
theorem tensorPointEvaluation_separates_pair (x y : A ⊗[k] B)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ p : B →ₐ[k] k, tensorPointEvaluation p x ≠ 0 ∧ tensorPointEvaluation p y ≠ 0 := by
  classical
  let e := Basis.ofVectorSpace k A
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := B) e
  have hex : ∃ i, E x i ≠ 0 := by
    by_contra! h
    apply hx
    apply E.injective
    ext i
    simpa using h i
  have hey : ∃ i, E y i ≠ 0 := by
    by_contra! h
    apply hy
    apply E.injective
    ext i
    simpa using h i
  obtain ⟨i, hi⟩ := hex
  obtain ⟨j, hj⟩ := hey
  obtain ⟨p, hpi, hpj⟩ := exists_algebraic_point_avoiding_pair (k := k) (E x i) (E y j) hi hj
  refine ⟨p, ?_, ?_⟩
  · intro h
    apply hpi
    rw [← tensorPointEvaluation_coordinate e p x i, h, map_zero, Finsupp.zero_apply]
  · intro h
    apply hpj
    rw [← tensorPointEvaluation_coordinate e p y j, h, map_zero, Finsupp.zero_apply]

theorem algebraic_tensor_noZeroDivisors : NoZeroDivisors (A ⊗[k] B) := by
  refine ⟨fun {x y} h => ?_⟩
  by_contra! hn
  obtain ⟨p, hx, hy⟩ := tensorPointEvaluation_separates_pair x y hn.1 hn.2
  apply mul_ne_zero hx hy
  rw [← map_mul, h, map_zero]

theorem algebraic_tensor_isDomain : IsDomain (A ⊗[k] B) := by
  letI := algebraic_tensor_noZeroDivisors (k := k) (A := A) (B := B)
  obtain ⟨p⟩ := nonempty_algebraic_point (k := k) (S := B)
  letI : Nontrivial (A ⊗[k] B) := ⟨⟨0, 1, fun h => by
    have hh := congrArg (tensorPointEvaluation (A := A) p) h
    exact zero_ne_one (by simpa only [map_zero, map_one] using hh)⟩⟩
  exact NoZeroDivisors.to_isDomain _

end StrictEUnit
#print axioms StrictEUnit.tensorPointEvaluation
#print axioms StrictEUnit.tensorPointEvaluation_tmul
#print axioms StrictEUnit.tensorPointEvaluation_coordinate
#print axioms StrictEUnit.tensorPointEvaluation_separates_pair
#print axioms StrictEUnit.algebraic_tensor_noZeroDivisors
#print axioms StrictEUnit.algebraic_tensor_isDomain
