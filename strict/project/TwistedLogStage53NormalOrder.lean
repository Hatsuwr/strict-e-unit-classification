import ConnectionStage53NormalOrder

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

/-- Actual ordinary derivative of an external rho-twisted finite-log amplitude.
This is a connection, not a derivation of the amplitude coefficient ring. -/
def actualTwistedLogOrdinary (rho : K) :
    Polynomial (LaurentSeries K) →ₗ[K] Polynomial (LaurentSeries K) where
  toFun y := stage61_logOrdinaryDerivation 1 y + Polynomial.C (HahnSeries.single (-1 : ℤ) rho)*y
  map_add' x y := by rw [map_add,mul_add];abel
  map_smul' c y := by
    rw [Derivation.map_smul]
    simp only [RingHom.id_apply,Algebra.smul_def]
    ring

theorem actualTwistedLogOrdinary_leibniz (rho : K)
    (x y : Polynomial (LaurentSeries K)) :
    actualTwistedLogOrdinary rho (x*y)=stage61_logOrdinaryDerivation 1 x*y+
      x*actualTwistedLogOrdinary rho y := by
  change stage61_logOrdinaryDerivation 1 (x*y)+_= _
  rw [Derivation.leibniz]
  simp only [actualTwistedLogOrdinary,smul_eq_mul,LinearMap.coe_mk,AddHom.coe_mk]
  ring

/-- Exact EXISTING Stage53 tuple on actual twisted logarithmic amplitudes.
No fractional power or rationality of rho is assumed. -/
theorem actualTwistedLogOrdinary_stage53 {mu nu : ℕ} (rho : K)
    (a : Fin (mu+1) →Fin (nu+1) →K) (y : Polynomial (LaurentSeries K)) :
    (∑ i,∑ j,algebraMap K (Polynomial (LaurentSeries K)) ((-1 : K)^j.val*a i j)*
      (actualTwistedLogOrdinary rho)^[j.val] ((stage38_sourceCoordinate (K:=K) 1)^i.val*y)) =
      ∑ l,Polynomial.aeval (stage38_sourceCoordinate (K:=K) 1) (stage53_fourierCoeff a l)*
        (actualTwistedLogOrdinary rho)^[l.val] y := by
  exact connection_stage53_normal_ordering (stage61_logOrdinaryDerivation 1)
    (actualTwistedLogOrdinary rho) (actualTwistedLogOrdinary_leibniz rho)
    (stage38_sourceCoordinate (K:=K) 1) (stage61_logOrdinary_coordinate 1 (by norm_num)) a y

end StrictEUnit
end
