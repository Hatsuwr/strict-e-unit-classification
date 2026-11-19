import Stage19GeneratedUnitClassification
import Stage17ArithmeticFrameODE
import StrictEZeroSetClassification

/-!
The intended positive power pullback F(t^N) is an actual bounded arithmetic
entire matrix, even when it is not itself strict-E. Arithmetic coefficients
come from the proved genuine power pullback, and growth degree N from the
original strict-E entries. The formal matrix is identified exactly with the
Stage17 ramified Taylor matrix. Original-frame punctured determinant
nonvanishing remains explicit here and is supplied by the Stage16 frame
results when the appropriate actual frame equation is given.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
section Matrix
variable (k : Subfield ℂ) (N : ℕ) (hN : N ≠ 0)
    {n : Type*}
    (F : Matrix n n (subfieldEntireFunctionAlgebra k))
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)

/-- The genuine ramified functions, with actual arithmetic Taylor coefficients
and growth degree N. No strict-E predicate is asserted for the pullback. -/
def stage19_ramifiedBoundedMatrix :
    Matrix n n (stage18_boundedArithmeticEntireAlgebra k N) :=
  fun i j => stage18_boundArithmeticFunction k N
    (stage17_arithmeticPowerPullback k N hN (F i j))
    (strictEFunction_powerExponentialBound (hstrict i j) N)

/-- The packaged entry is literally the original function composed with z^N. -/
@[simp] theorem stage19_ramifiedBoundedMatrix_apply (i j : n) (z : ℂ) :
    (stage19_ramifiedBoundedMatrix k N hN F hstrict i j).val z =
      (F i j).val.val (z^N) := rfl

/-- The generated algebra uses exactly the ramified formal Taylor matrix
already constructed in Stage17, not an assumed isomorphic replacement. -/
theorem stage19_ramifiedFormalMatrix_compatibility :
    (stage19_formalMatrix k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)).map RatFunc.C =
      stage17_formalFrame k N hN F := by
  ext i j
  rfl

variable [Fintype n] [DecidableEq n]

/-- The determinant is exactly the original actual determinant evaluated at z^N. -/
theorem stage19_ramifiedBoundedMatrix_det_apply (z : ℂ) :
    (stage19_ramifiedBoundedMatrix k N hN F hstrict).det.val z =
      (F.map (stage14_subfieldEntireEvaluation k (z^N))).det := by
  let e : stage18_boundedArithmeticEntireAlgebra k N →ₐ[k] ℂ :=
    (stage14_subfieldEntireEvaluation k z).comp (stage18_boundedToArithmeticAlgHom k N)
  change e.toRingHom (stage19_ramifiedBoundedMatrix k N hN F hstrict).det = _
  rw [RingHom.map_det]
  rfl

/-- Original-frame nonvanishing off zero propagates through the genuine power
pullback because z != 0 implies z^N != 0. -/
theorem stage19_ramifiedBoundedMatrix_det_nonzero
    (hd : ∀ z : ℂ, z ≠ 0 → (F.map (stage14_subfieldEntireEvaluation k z)).det ≠ 0) :
    ∀ z : ℂ, z ≠ 0 → (stage19_ramifiedBoundedMatrix k N hN F hstrict).det.val z ≠ 0 := by
  intro z hz
  rw [stage19_ramifiedBoundedMatrix_det_apply]
  exact hd (z^N) (pow_ne_zero _ hz)

variable (hd : ∀ z : ℂ, z ≠ 0 → (F.map (stage14_subfieldEntireEvaluation k z)).det ≠ 0)

/-- The actual coefficient-algebra evaluation for the intended ramified frame,
normalized at t=1. It is constructed using the genuine localization. -/
def stage19_ramifiedGeneratedEvaluation :
    formalMatrixCoefficientAlgebra
      (stage19_formalMatrix k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)) →ₐ[k] ℂ :=
  stage19_generatedEvaluation k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)
    (stage19_ramifiedBoundedMatrix_det_nonzero k N hN F hstrict hd) ⟨1, one_ne_zero⟩

/-- Ramification leaves each original entry value at one unchanged. -/
theorem stage19_ramifiedGeneratedEvaluation_entry (i j : n) :
    stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd
      (stage19_generatedEntry k N (stage19_ramifiedBoundedMatrix k N hN F hstrict) i j) =
      (F i j).val.val 1 := by
  simpa only [stage19_ramifiedBoundedMatrix_apply, one_pow] using
    stage19_generatedEvaluation_entry k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)
      (stage19_ramifiedBoundedMatrix_det_nonzero k N hN F hstrict hd) i j ⟨1, one_ne_zero⟩

/-- The intended ramified coefficient-unit value is an arithmetic scalar
exponential. Growth degree N is derived, and N != 0 supplies its positivity. -/
theorem stage19_ramifiedGenerated_unit_value
    (u : formalMatrixCoefficientAlgebra
      (stage19_formalMatrix k N (stage19_ramifiedBoundedMatrix k N hN F hstrict)))
    (hu : IsUnit u) :
    ∃ c a : k, c ≠ 0 ∧
      stage19_ramifiedGeneratedEvaluation k N hN F hstrict hd u =
        (c : ℂ) * Complex.exp (a : ℂ) :=
  stage19_generated_unit_at_one_eq_subfield_scalar_exp k N
    (stage19_ramifiedBoundedMatrix k N hN F hstrict)
    (stage19_ramifiedBoundedMatrix_det_nonzero k N hN F hstrict hd)
    (Nat.pos_of_ne_zero hN) u hu

end Matrix
end StrictEUnit
