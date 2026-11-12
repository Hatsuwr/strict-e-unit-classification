import FiniteLaurentForcingArithmetic
import SelectedSourceForcingArithmetic

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Original source arithmetic survives adjoining a constant coefficient for
any fixed finite integer Laurent forcing family, including negative modes. -/
theorem selectedFuchsSourceData_finite_laurent_forcing_arithmetic
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (c : Fin r →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi r hr c T UI E) (k : ℕ →ℤ) (s : ℕ) :
    LaurentDividedConnectionArithmetic (finiteLaurentForcingConnection
      (Matrix.map (minimalDerivativeCompanion r c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (sourcePolynomialForcingColumn r T) k s) := by
  exact finiteLaurentForcingConnection_arithmetic _ _
    (selectedFuchsSourceData_laurent_connection_arithmetic G a phi r hr c T UI E hsource)
    (sourcePolynomialForcingColumn_arithmetic r T hsource.2.1) k s

end StrictEUnit
end
