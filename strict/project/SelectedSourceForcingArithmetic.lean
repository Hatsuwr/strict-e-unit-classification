import IntegralPolynomialForcingArithmetic
import RationalLaurentConnectionTransport

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Extract both the genuine linear pole bound and common exponential
arithmetic for the ORIGINAL selected Laurent companion. -/
theorem selectedFuchsSourceData_laurent_connection_arithmetic
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi r hr c T UI E) :
    LaurentDividedConnectionArithmetic
      (Matrix.map (minimalDerivativeCompanion r c) (algebraMap (RatFunc K) (LaurentSeries K))) := by
  have hsing := selectedFuchsSourceData_singular_connection_arithmetic G a phi r hr c T UI E hsource
  obtain ⟨hclear,hid,hq,hqE,htri,hC,hden⟩ := hsing
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
  let q := Int.natAbs (Algebra.norm ℤ (T.coeff t.natTrailingDegree))
  refine ⟨t.natTrailingDegree,((q : ℝ)*E)^(t.natTrailingDegree+2),hC,?_,?_⟩
  · intro m i j l hl
    rw [rational_laurent_divided_connection]
    rw [powerSeries_monomial_laurent_coefficient
      (samePoleClearedDividedConnectionGerm t U m i j) _ (t.natTrailingDegree*m) (hid m i j) l,
      dif_neg (by omega)]
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    refine ⟨D,hD,hDb,?_⟩
    intro m hm i j l hl
    rw [rational_laurent_divided_connection]
    exact hDi m hm l hl i j

/-- All finite polynomial-forcing chains for the SAME source inherit proved
operator arithmetic. No desired Fourier solution arithmetic is supplied. -/
theorem selectedFuchsSourceData_polynomial_forcing_arithmetic
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi r hr c T UI E) (d : ℕ) :
    LaurentDividedConnectionArithmetic (polynomialForcingConnection
      (Matrix.map (minimalDerivativeCompanion r c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (sourcePolynomialForcingColumn r T) d) := by
  apply polynomialForcingConnection_arithmetic
  · exact selectedFuchsSourceData_laurent_connection_arithmetic G a phi r hr c T UI E hsource
  · exact sourcePolynomialForcingColumn_arithmetic r T hsource.2.1

end StrictEUnit
end
