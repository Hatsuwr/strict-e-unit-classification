import Stage17ArithmeticFrameODE

noncomputable section
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
variable (k : Subfield ℂ) {n : Type*} [Fintype n] [DecidableEq n]

def stage17_formalBaseMatrixUnit (Z : (Matrix n n (LaurentLogBase k))ˣ) :
    (Matrix n n (RatFunc (LaurentSeries k)))ˣ :=
  Units.map formalBaseEmbedding.toRingHom.mapMatrix.toMonoidHom Z

end StrictEUnit
end
