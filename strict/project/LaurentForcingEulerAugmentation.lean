import ActualLogFrameSpanning
import Mathlib.LinearAlgebra.Matrix.Block

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Euler eigenvectors include negative Laurent powers; no differentiation
nilpotence is required for the forcing. -/
theorem coefficientEuler_constant_monomial (k : ℤ) (c : K) :
    polynomialCoefficientEuler 1 (HahnSeries.single k (Polynomial.C c))=
      (k:K) • HahnSeries.single k (Polynomial.C c) := by
  apply HahnSeries.ext
  funext n
  change (n:K) • (HahnSeries.single k (Polynomial.C c)).coeff n+
    (1:K) • ((HahnSeries.single k (Polynomial.C c)).coeff n).derivative=_
  rw [HahnSeries.coeff_smul]
  by_cases h : n=k
  · subst n
    simp only [HahnSeries.coeff_single_same,Polynomial.derivative_C,smul_zero,add_zero]
  · simp only [HahnSeries.coeff_single_of_ne h,Polynomial.derivative_zero,smul_zero,add_zero]

/-- A regular Euler block matrix for finite Laurent-polynomial forcing.
Negative forcing exponents enter the constant residue, never as coefficient
poles. This construction asserts no connection-arithmetic bound. -/
def laurentForcingEulerMatrix {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (k : Fin s →ℤ) :
    Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) (PowerSeries K) :=
  Matrix.fromBlocks C (fun i _ =>g i) 0
    (Matrix.diagonal (fun j =>PowerSeries.C K (k j:K)))

def laurentForcingEulerVector {r s : ℕ}
    (u : Fin r →LaurentSeries (Polynomial K)) (k : Fin s →ℤ) (c : Fin s →K) :
    (Fin r ⊕ Fin s) →LaurentSeries (Polynomial K) :=
  Sum.elim u (fun j =>HahnSeries.single (k j) (Polynomial.C (c j)))

/-- Exact scalar-forcing to homogeneous-vector lift for any finite integer
exponent set, including the negative modes left by reciprocal gauge undoing. -/
theorem laurentForcingEulerVector_solution {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (k : Fin s →ℤ) (c : Fin s →K) (u : Fin r →LaurentSeries (Polynomial K))
    (hu : ∀ i,polynomialCoefficientEuler 1 (u i)=
      (∑ j,logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (C i j))*u j)+
      logPolynomialToCoefficientSeries (logPowerSeriesEmbedding (g i))*
        ∑ j,HahnSeries.single (k j) (Polynomial.C (c j))) :
    ∀ i,polynomialCoefficientEuler 1 (laurentForcingEulerVector u k c i)=
      ∑ j,logPolynomialToCoefficientSeries
        (logPowerSeriesEmbedding (laurentForcingEulerMatrix C g k i j))*
        laurentForcingEulerVector u k c j := by
  classical
  intro i
  cases i with
  | inl i =>
    simpa only [Fintype.sum_sum_type,laurentForcingEulerVector,Sum.elim_inl,Sum.elim_inr,
      laurentForcingEulerMatrix,Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
      Finset.mul_sum] using hu i
  | inr i =>
    simp only [Fintype.sum_sum_type,laurentForcingEulerVector,Sum.elim_inl,Sum.elim_inr,
      laurentForcingEulerMatrix,Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply,Pi.zero_apply,map_zero,zero_mul,Finset.sum_const_zero,zero_add]
    rw [coefficientEuler_constant_monomial,laurentCoefficient_smul_eq_mul]
    simp only [Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ite_true]
      have he : logPolynomialToCoefficientSeries
          (logPowerSeriesEmbedding (PowerSeries.C K (k i:K)))=
          HahnSeries.single 0 (Polynomial.C (k i:K)) := by
        simp only [map_intCast,← HahnSeries.C_apply]
      rw [he]
    · intro b hb hbi
      rw [if_neg (Ne.symm hbi),map_zero,map_zero,zero_mul]
    · simp

end StrictEUnit
end
