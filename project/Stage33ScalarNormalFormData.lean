import RamifiedBaseMatrix
import Stage33ScalarNormalFormRowData

noncomputable section
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit

structure Stage33ScalarNormalForm (k : Subfield ℂ) (m : ℕ)
    (p : Fin (m + 1) → Polynomial k) where
  N : ℕ
  ramification_ne_zero : N ≠ 0
  e : Fin m → subfieldEntireFunctionAlgebra k
  M : Matrix (Fin m) (Fin m) k
  Z : (Matrix (Fin m) (Fin m) (LaurentLogBase k))ˣ
  strict : ∀ j, IsStrictEFunction (e j).val.val
  rational : ∀ a : k, (minpoly k M).IsRoot a → ∃ q : ℚ, (q : k) = a
  base_equation : matrixDerivative (manuscriptBaseDerivation (k := k) N) Z.val =
    ramifiedConstantMatrix M * Z.val
  scalar_equation : ∀ j, ∑ l,
    Polynomial.aeval
      (stage17_ramifiedEntireFormalAlgHom k N ramification_ne_zero (subfieldEntireCoordinate k))
      (p l) *
      ((stage32_ramifiedOrdinaryDerivation k N ramification_ne_zero) :
        RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k))^[l.val]
          (stage33_scalarNormalFormRow k N ramification_ne_zero e Z j) = 0
  independent : LinearIndependent k
    (stage33_scalarNormalFormRow k N ramification_ne_zero e Z)

end StrictEUnit
end
