import Stage15StrictEEulerClosure
import Stage15StrictEDeterminantClassification
import Stage28LaurentCompanion

/-! Actual entire rows for pole-cleared ordinary jets. All exponents in the
frame are natural numbers, and full strict-E closure is proved over Qbar. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit

local instance (k : Subfield ℂ) : CommRing (subfieldEntireFunctionAlgebra k) :=
  (subfieldEntireFunctionAlgebra k).toCommRing
local instance (k : Subfield ℂ) : AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _ (subfieldEntireFunctionAlgebra k).toSemiring))

variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

/-- The integer residue shift, in the original coefficient matrix algebra. -/
def stage33_shiftedResidue (M : Matrix n n k) (s : ℕ) : Matrix n n k :=
  M - algebraMap k (Matrix n n k) (s : k)

/-- Actual entire recursive rows: U₀=e and Uᵢ₊₁=z Uᵢ′+Uᵢ(M-iI). -/
def stage33_entireJetRow (e : n → subfieldEntireFunctionAlgebra k)
    (M : Matrix n n k) : ℕ → n → subfieldEntireFunctionAlgebra k
  | 0 => e
  | i + 1 => fun j =>
      subfieldEntireCoordinate k * subfieldEntireFunctionDerivation k
        (stage33_entireJetRow e M i j) +
      ∑ l, stage33_entireJetRow e M i l *
        algebraMap k (subfieldEntireFunctionAlgebra k) (stage33_shiftedResidue k M i l j)

/-- The genuine entire frame, with a common shift s=m-1. -/
def stage33_entireJetFrame (m : ℕ)
    (e : Fin m → subfieldEntireFunctionAlgebra k) (M : Matrix (Fin m) (Fin m) k) :
    Matrix (Fin m) (Fin m) (subfieldEntireFunctionAlgebra k) :=
  fun i j => subfieldEntireCoordinate k ^ (m - 1 - i.val) *
    stage33_entireJetRow k e M i.val j

/-- The exponent in the whole-plane frame clears each actual jet pole. -/
theorem stage33_frame_exponent_add (m : ℕ) (i : Fin m) :
    (m - 1 - i.val) + i.val = m - 1 := by omega

/-- Forgetting the arithmetic entire-function structure preserves ring operations. -/
def stage33_entireFunctionValue : subfieldEntireFunctionAlgebra k →+* (ℂ → ℂ) :=
  entireFunctionAlgebra.val.toRingHom.comp (subfieldEntireFunctionAlgebra k).val.toRingHom

/-- Every algebraic constant in the exact coefficient field is full strict E. -/
theorem stage33_strictE_arithmetic_constant (a : (algebraicClosure ℚ ℂ).toSubfield) :
    IsStrictEFunction
      (algebraMap (algebraicClosure ℚ ℂ).toSubfield
        (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) a).val.val := by
  exact algebraic_constant_isStrictEFunction a

/-- The entire recursion preserves all arithmetic, analytic and ODE clauses. -/
theorem stage33_entireJetRow_strict
    (e : n → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (M : Matrix n n (algebraicClosure ℚ ℂ).toSubfield)
    (he : ∀ j, IsStrictEFunction (e j).val.val) (i : ℕ) (j : n) :
    IsStrictEFunction
      (stage33_entireJetRow (algebraicClosure ℚ ℂ).toSubfield e M i j).val.val := by
  induction i generalizing j with
  | zero => exact he j
  | succ i ih =>
    change stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield
      (_ + _) ∈ strictEFunctionSubring
    have hsum (g : n → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :
        stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield (∑ l, g l) =
          ∑ l, stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield (g l) :=
      map_sum (stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield).toAddMonoidHom g Finset.univ
    rw [(stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield).map_add, hsum]
    apply strictEFunctionSubring.add_mem
    · exact strictEFunction_eulerDerivative (ih j)
    · apply strictEFunctionSubring.sum_mem
      intro l hl
      rw [map_mul]
      exact strictEFunction_mul (ih l) (stage33_strictE_arithmetic_constant _)

/-- Multiplication by the nonnegative coordinate powers preserves full strict E. -/
theorem stage33_entireJetFrame_strict (m : ℕ)
    (e : Fin m → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (M : Matrix (Fin m) (Fin m) (algebraicClosure ℚ ℂ).toSubfield)
    (he : ∀ j, IsStrictEFunction (e j).val.val) (i j : Fin m) :
    IsStrictEFunction
      (stage33_entireJetFrame (algebraicClosure ℚ ℂ).toSubfield m e M i j).val.val := by
  change stage33_entireFunctionValue (algebraicClosure ℚ ℂ).toSubfield
    (_ ^ _ * _) ∈ strictEFunctionSubring
  rw [map_mul, map_pow]
  apply strictEFunctionSubring.mul_mem
  · exact strictEFunctionSubring.pow_mem strictEFunction_coordinate _
  · exact stage33_entireJetRow_strict e M he i.val j

end StrictEUnit
