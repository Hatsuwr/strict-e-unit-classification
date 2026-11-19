import Stage15DeterminantNonvanishing
import Stage14StrictERingClosure
import StrictEZeroSetClassification

/-! The genuine determinant consequence: strict-E entries and an actual
regular first-order matrix system give an algebraic scalar times z^m exp(a z).
The existence of the manuscript's frame/system is not asserted here. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- The actual strict E-functions, with their full defining conditions, form
a subring of the actual complex-valued function ring. -/
def strictEFunctionSubring : Subring (ℂ → ℂ) where
  carrier := {f | IsStrictEFunction f}
  zero_mem' := by simpa using algebraic_constant_isStrictEFunction (0 : AlgebraicComplex)
  one_mem' := by simpa using algebraic_constant_isStrictEFunction (1 : AlgebraicComplex)
  add_mem' := strictEFunction_add
  mul_mem' := strictEFunction_mul
  neg_mem' := strictEFunction_neg

@[simp] theorem mem_strictEFunctionSubring (f : ℂ → ℂ) :
    f ∈ strictEFunctionSubring ↔ IsStrictEFunction f := Iff.rfl

/-- Finite determinants preserve the full actual strict-E predicate. -/
theorem strictEFunction_det {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n (ℂ → ℂ)) (hF : ∀ i j, IsStrictEFunction (F i j)) :
    IsStrictEFunction F.det := by
  let G : Matrix n n strictEFunctionSubring := fun i j => ⟨F i j, hF i j⟩
  have he : ((G.det : strictEFunctionSubring) : ℂ → ℂ) = F.det :=
    RingHom.map_det strictEFunctionSubring.subtype G
  rw [← he]
  exact G.det.property

/-- The determinant of actual entire functions is strict E whenever each
entry is strict E; this is not a closure assumption. -/
theorem strictEFunction_entireMatrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n entireFunctionAlgebra)
    (hF : ∀ i j, IsStrictEFunction (F i j).val) : IsStrictEFunction F.det.val := by
  have he : F.det.val = (F.map entireFunctionAlgebra.val).det :=
    RingHom.map_det entireFunctionAlgebra.val.toRingHom F
  rw [he]
  exact strictEFunction_det _ hF

/-- A strict-E function's actual regular first-order scalar equation and a
single nonzero value now imply the arithmetic origin-only-zero normal form. -/
theorem strictEFunction_firstOrder_exp_form
    (p q : Polynomial ℂ) {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (hp : ∀ z : ℂ, z ≠ 0 → p.eval z ≠ 0)
    (hode : ∀ z, z ≠ 0 → p.eval z * deriv f z = q.eval z * f z)
    (h1 : f 1 ≠ 0) :
    ∃ m : ℕ, ∃ c a : AlgebraicComplex,
      ((strictEFunction_differentiable hf).analyticAt 0).meromorphicAt.order =
        ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient f m ∧
      ∀ z, f z = (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) :=
  strictEFunction_origin_only_zero_exp_form hf
    (entire_polynomial_firstOrder_nonzero_off_origin_of_punctured p q
      (strictEFunction_differentiable hf) hp hode h1)

/-- A scalar first-order equation also supplies an actual strict-E
representative of the reciprocal value at one. -/
theorem strictEFunction_firstOrder_at_one_unit
    (p q : Polynomial ℂ) {f : ℂ → ℂ} (hf : IsStrictEFunction f)
    (hp : ∀ z : ℂ, z ≠ 0 → p.eval z ≠ 0)
    (hode : ∀ z, z ≠ 0 → p.eval z * deriv f z = q.eval z * f z)
    (h1 : f 1 ≠ 0) : IsStrictEValueUnit (f 1) :=
  strictEFunction_at_one_unit_of_origin_only_zeros hf
    (entire_polynomial_firstOrder_nonzero_off_origin_of_punctured p q
      (strictEFunction_differentiable hf) hp hode h1)

/-- The actual determinant arithmetic normal form follows from strict-E
entries, the matrix differential identity, ordinary-point regularity, and a
single nonzero determinant. Neither nonvanishing off zero nor a reciprocal
function is an input. -/
theorem strictE_entireMatrix_determinant_exp_form {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    ∃ m : ℕ, ∃ c a : AlgebraicComplex,
      (F.det.property.analyticAt 0).meromorphicAt.order = ((m : ℤ) : WithTop ℤ) ∧
      c ≠ 0 ∧ (c : ℂ) = entireCauchyCoefficient F.det.val m ∧
      ∀ z, (F.map (entireEvaluation z)).det =
        (c : ℂ) * z^m * Complex.exp ((a : ℂ)*z) := by
  have hf := strictEFunction_entireMatrix_det F hstrict
  have hnz : ∀ z : ℂ, z ≠ 0 → F.det.val z ≠ 0 := by
    intro z hz
    rw [entireMatrix_evaluation_det]
    exact entireMatrix_determinant_nonzero_off_origin_of_punctured p A F hF hp h1 z hz
  obtain ⟨m, c, a, hm, hc, hcoeff, hform⟩ :=
    strictEFunction_origin_only_zero_exp_form hf hnz
  refine ⟨m, c, a, hm, hc, hcoeff, fun z => ?_⟩
  rw [← entireMatrix_evaluation_det]
  exact hform z

/-- In particular the nonzero determinant value at one is a unit in the
actual numerical strict-E ring. -/
theorem strictE_entireMatrix_determinant_at_one_unit {n : Type*}
    [Fintype n] [DecidableEq n]
    (p : entireFunctionAlgebra) (A F : Matrix n n entireFunctionAlgebra)
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val)
    (hF : ∀ z, z ≠ 0 → ∀ i j, p.val z * deriv (F i j).val z =
      ∑ k, (A i k).val z * (F k j).val z)
    (hp : ∀ z : ℂ, z ≠ 0 → p.val z ≠ 0)
    (h1 : (F.map (entireEvaluation 1)).det ≠ 0) :
    IsStrictEValueUnit ((F.map (entireEvaluation 1)).det) := by
  rw [← entireMatrix_evaluation_det]
  apply strictEFunction_at_one_unit_of_origin_only_zeros (strictEFunction_entireMatrix_det F hstrict)
  intro z hz
  rw [entireMatrix_evaluation_det]
  exact entireMatrix_determinant_nonzero_off_origin_of_punctured p A F hF hp h1 z hz

end StrictEUnit
