import Stage17FormalBaseUnitData
import Stage32FormalToActualFrame

noncomputable section
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

def stage33_scalarNormalFormRow (N : ℕ) (hN : N ≠ 0)
    (e : n → subfieldEntireFunctionAlgebra k) (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    n → RatFunc (LaurentSeries k) :=
  fun j => ∑ l, stage17_ramifiedEntireFormalAlgHom k N hN (e l) *
    (stage17_formalBaseMatrixUnit k Z).val l j

end StrictEUnit
end
