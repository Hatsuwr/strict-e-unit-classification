import LaurentForcingEulerAugmentation
import Mathlib.LinearAlgebra.Vandermonde

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def forcingMomentMatrix {s : ℕ} (lam : Fin s → K) : Matrix (Fin s) (Fin s) K :=
  (Matrix.vandermonde lam).transpose

theorem forcingMomentMatrix_det_ne_zero {s : ℕ} (lam : Fin s → K)
    (hlam : Function.Injective lam) : (forcingMomentMatrix lam).det ≠ 0 := by
  rw [forcingMomentMatrix, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hlam

/-- The actual residual exponents d-j remain distinct after the common gauge shift. -/
theorem shiftedResidualEigenvalues_injective (s : ℕ) (b d : ℤ) :
    Function.Injective (fun j : Fin s => ((b+d-(j.val:ℤ):ℤ):K)) := by
  intro i j h
  apply Fin.ext
  have hi : b+d-(i.val:ℤ)=b+d-(j.val:ℤ) := Int.cast_injective h
  omega

def forcingMoment {s : ℕ} (lam : Fin s → K)
    (h : Fin s → LaurentSeries (Polynomial K)) (m : ℕ) :
    LaurentSeries (Polynomial K) := ∑ j, (lam j)^m • h j

theorem coefficientEuler_smul (c : K) (f : LaurentSeries (Polynomial K)) :
    polynomialCoefficientEuler 1 (c • f)=c • polynomialCoefficientEuler 1 f := by
  apply HahnSeries.ext
  funext n
  change (n:K) • (c • f).coeff n+(1:K) • ((c • f).coeff n).derivative=_
  simp only [HahnSeries.coeff_smul, Polynomial.smul_eq_C_mul, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, one_smul]
  change _=Polynomial.C c*((n:K) • f.coeff n+(1:K) • (f.coeff n).derivative)
  simp only [one_smul, Polynomial.smul_eq_C_mul]
  ring

theorem forcingMoment_euler {s : ℕ} (lam : Fin s → K)
    (h : Fin s → LaurentSeries (Polynomial K))
    (hh : ∀ j,polynomialCoefficientEuler 1 (h j)=lam j • h j) (m : ℕ) :
    polynomialCoefficientEuler 1 (forcingMoment lam h m)=forcingMoment lam h (m+1) := by
  change coefficientEulerAdd (∑ j, (lam j)^m • h j)=_
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change polynomialCoefficientEuler 1 (_ • _)=_
  rw [coefficientEuler_smul,hh j,smul_smul,pow_succ]

theorem forcingMoment_zero {s : ℕ} (lam : Fin s → K)
    (h : Fin s → LaurentSeries (Polynomial K)) : forcingMoment lam h 0=∑ j,h j := by
  simp [forcingMoment]

/-- Any explicitly verified annihilating relation closes the moment chain.
No distinctness or arithmetic assertion is hidden in this identity. -/
theorem forcingMoment_closure {s : ℕ} (lam a : Fin s → K)
    (h : Fin s → LaurentSeries (Polynomial K))
    (ha : ∀ j,(lam j)^s=∑ m : Fin s,a m*(lam j)^m.val) :
    forcingMoment lam h s=∑ m : Fin s,a m • forcingMoment lam h m.val := by
  apply HahnSeries.ext
  funext n
  simp only [forcingMoment,HahnSeries.coeff_sum,HahnSeries.coeff_smul]
  simp_rw [ha]
  simp only [Finset.sum_smul,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

end StrictEUnit
end
