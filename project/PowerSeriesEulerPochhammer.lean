import SameCompanionPowerSeriesJetTransport
import RegularResidueIndicialRoots
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
The actual power-series Euler operator and the falling-Pochhammer identity.
The SAME regular scalar coefficients are recorded as a polynomial whose
coefficients act on the left. That polynomial is not evaluated at a falsely
power-series-linear Euler endomorphism. SOURCE ONLY until the serial replay.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The actual X*d/dX operator, bundled only as a K-linear endomorphism. -/
def powerSeriesEulerLinear {K : Type*} [CommSemiring K] :
    Module.End K (PowerSeries K) :=
  ((PowerSeries.X : PowerSeries K) • PowerSeries.derivative K).toLinearMap

@[simp] theorem powerSeriesEulerLinear_apply {K : Type*} [CommSemiring K]
    (f : PowerSeries K) :
    powerSeriesEulerLinear f=powerSeriesEuler f := rfl

/-- Falling polynomials of the actual Euler map are the literal weighted
ordinary derivatives. No inverse of X, characteristic restriction or shift
of the Euler derivation is used. -/
theorem powerSeriesEulerLinear_descPochhammer
    {K : Type*} [CommRing K] (m : ℕ) (f : PowerSeries K) :
    Polynomial.aeval (powerSeriesEulerLinear (K := K)) (descPochhammer K m) f=
      weightedDerivativeJet m f := by
  induction m with
  | zero => simp [descPochhammer_zero,weightedDerivativeJet]
  | succ m ih =>
    have hleft : descPochhammer K (m+1)=
        (Polynomial.X-Polynomial.C (m:K))*descPochhammer K m := by
      rw [descPochhammer_succ_right,Polynomial.C_eq_natCast,mul_comm]
    rw [hleft,map_mul,Module.End.mul_apply,ih]
    simp only [map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
      LinearMap.sub_apply,Module.algebraMap_end_apply,powerSeriesEulerLinear_apply]
    rw [weightedDerivativeJet_euler]
    simp only [Algebra.smul_def,map_natCast]
    ring

/-- Coefficient polynomial of the SAME regular scalar Euler operator.
Its coefficients are power series and must act on the left. -/
def sameCompanionEulerPochhammerPolynomial
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    Polynomial (PowerSeries K) :=
  descPochhammer (PowerSeries K) (n+1)-
    ∑ j : Fin (n+1),Polynomial.C (sameCompanionEulerLastRowSeries n T U j)*
      descPochhammer (PowerSeries K) j.val

/-- Constant specialization is literally the already constructed residue
indicial polynomial, with the original trailing coefficient and face. -/
@[simp] theorem sameCompanionEulerPochhammerPolynomial_constantCoeff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (sameCompanionEulerPochhammerPolynomial n T U).map (PowerSeries.constantCoeff K)=
      regularResidueIndicial n (T.coeff T.natTrailingDegree)
        (polynomialCompanionFace n 1 1 T U) := by
  classical
  simp only [sameCompanionEulerPochhammerPolynomial,regularResidueIndicial,
    Polynomial.map_sub,Polynomial.map_sum,Polynomial.map_mul,Polynomial.map_C,
    descPochhammer_map,sameCompanionEulerLastRowSeries_constantCoeff]

theorem sameCompanionEulerPochhammerPolynomial_lower_natDegree_le
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (∑ j : Fin (n+1),Polynomial.C (sameCompanionEulerLastRowSeries n T U j)*
      descPochhammer (PowerSeries K) j.val).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [descPochhammer_natDegree]
  exact Nat.le_of_lt_succ j.isLt

/-- The polynomial has the actual positive source order n+1. -/
theorem sameCompanionEulerPochhammerPolynomial_natDegree
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (sameCompanionEulerPochhammerPolynomial n T U).natDegree=n+1 := by
  have hlow := sameCompanionEulerPochhammerPolynomial_lower_natDegree_le n T U
  have hlt :
      (∑ j : Fin (n+1),Polynomial.C (sameCompanionEulerLastRowSeries n T U j)*
        descPochhammer (PowerSeries K) j.val).natDegree <
      (descPochhammer (PowerSeries K) (n+1)).natDegree := by
    rw [descPochhammer_natDegree]
    exact Nat.lt_succ_of_le hlow
  exact (Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt).trans
    (descPochhammer_natDegree (PowerSeries K) (n+1))

theorem sameCompanionEulerPochhammerPolynomial_top_coeff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (sameCompanionEulerPochhammerPolynomial n T U).coeff (n+1)=1 := by
  have hlow := sameCompanionEulerPochhammerPolynomial_lower_natDegree_le n T U
  rw [sameCompanionEulerPochhammerPolynomial,
    Polynomial.coeff_sub_eq_left_of_lt (Nat.lt_succ_of_le hlow)]
  simpa only [descPochhammer_natDegree] using
    (monic_descPochhammer (PowerSeries K) (n+1)).coeff_natDegree

theorem sameCompanionEulerPochhammerPolynomial_monic
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (sameCompanionEulerPochhammerPolynomial n T U).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one (n+1)
  · exact le_of_eq (sameCompanionEulerPochhammerPolynomial_natDegree n T U)
  · exact sameCompanionEulerPochhammerPolynomial_top_coeff n T U

end StrictEUnit
end
