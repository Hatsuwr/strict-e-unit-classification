import LogFilteredFiniteJetArithmetic
import LaurentMatrixPrefixCancellation

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Multi-class finite-prefix annihilation transfers to the SAME connection
matrix through a genuine supplied fundamental right inverse. Constructing this
matrix/inverse for the original selected family remains an explicit task. -/
theorem allClassPrefixFilter_connection_prefix_zero {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (J : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j)
    (hJ : (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))*J=1)
    (L W : ℤ) (d : ℕ)
    (hYlow : ∀ i j a,a<L →(logPolynomialToCoefficientSeries (Y i j)).coeff a=0)
    (hYdeg : ∀ i j a,((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree≤d)
    (hJlow : ∀ i j a,a< -W →(J i j).coeff a=0) (N : ℕ) :
    ∀ i j a,a<L+(N : ℤ)-W →
      (HahnSeries.ofPowerSeries ℤ K
        (powerSeriesEulerPolynomialConnection C (allClassPrefixFilter rho L N d) i j)).coeff a=0 := by
  let P := allClassPrefixFilter rho L N d
  let F : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)) := fun i j =>
    logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (powerSeriesEulerPolynomialConnection C P i j))
  let H : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)) := fun i j =>
    logPolynomialToCoefficientSeries (Y i j)
  let Z : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)) := fun i j =>
    logPolynomialToCoefficientSeries (literalLogPolynomialFilter (rho j) P (Y i j))
  have hF : F*H=Z := by
    funext i j
    have he := congrArg logPolynomialToCoefficientSeries
      (literalLogPolynomialFilter_solution_identity C (rho j) (fun i =>Y i j) (hY j) P i)
    simpa only [F,H,Z,Matrix.mul_apply,map_sum,map_mul] using he.symm
  have hZ : ∀ i j a,a<L+(N : ℤ) →(Z i j).coeff a=0 := by
    intro i j a ha
    exact allClassPrefixFilter_literal_prefix_zero rho L N d j (Y i j) (hYlow i j) (hYdeg i j) a ha
  have h := laurentMatrix_prefix_cancel_right F H J Z hF hJ (L+(N : ℤ)) (-W) hZ hJlow
  intro i j a ha
  have hf := h i j a (by omega)
  change (logPolynomialToCoefficientSeries (Polynomial.C (HahnSeries.ofPowerSeries ℤ K
    (powerSeriesEulerPolynomialConnection C P i j)))).coeff a=0 at hf
  rw [logPolynomialToCoefficientSeries_C,logLaurentCoefficientMap_coeff] at hf
  apply Polynomial.C_injective
  simpa only [map_zero] using hf

/-- With that inverse and its FIXED pole bound, filtered-solution arithmetic
uses only a fixed initial jet. No denominator bound on the unknown full
solution sequence or on the filtered coefficients is assumed. -/
theorem allClassPrefixFilter_solution_finite_jet_integral {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : Fin r → K)
    (Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)))
    (J : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)))
    (hY : ∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j)
    (hJ : (Matrix.of (fun i j =>logPolynomialToCoefficientSeries (Y i j)))*J=1)
    (L W : ℤ) (d : ℕ)
    (hYlow : ∀ i j a,a<L →(logPolynomialToCoefficientSeries (Y i j)).coeff a=0)
    (hYdeg : ∀ i j a,((logPolynomialToCoefficientSeries (Y i j)).coeff a).natDegree≤d)
    (hJlow : ∀ i j a,a< -W →(J i j).coeff a=0)
    (s : Fin r) (N : ℕ) (D e : K)
    (hFden : ∀ i j k,k≤N →IsIntegral ℤ (D*PowerSeries.coeff K k
      (powerSeriesEulerPolynomialConnection C (allClassPrefixFilter rho L N d) i j)))
    (hjet : ∀ j t k,k≤W →IsIntegral ℤ (e*((Y j s).coeff t).coeff k))
    (i : Fin r) (t : ℕ) :
    IsIntegral ℤ (D*e*((literalLogPolynomialFilter (rho s)
      (allClassPrefixFilter rho L N d) (Y i s)).coeff t).coeff ((N : ℤ)+L)) := by
  apply literalLogPolynomialFilter_finite_jet_integral C (rho s) (fun i =>Y i s) (hY s)
    (allClassPrefixFilter rho L N d) N L W D e ?_ ?_ hFden hjet i t
  · intro i j k hk
    exact allClassPrefixFilter_connection_prefix_zero C rho Y J hY hJ L W d hYlow hYdeg hJlow N i j k (by omega)
  · intro j t k hk
    rw [← logPolynomialToCoefficientSeries_double_coeff,hYlow j s k hk,Polynomial.coeff_zero]

end StrictEUnit
end
