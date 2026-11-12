import OrdinaryPointPowerSeries
import FormalFundamentalMatrixUnit
import Mathlib.RingTheory.Localization.Integer

/-! Choose one common polynomial denominator for the SAME rational matrix,
then one ordinary point, and construct the translated power-series matrix.
The final theorem also constructs its normalized formal fundamental matrix.
No matrix regularity, chosen ordinary point, solution or inverse is assumed. -/
noncomputable section
open scoped Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] {r : ℕ}

/-- A finite rational matrix has one ordinary point and a literal power-series
realization under the previously constructed injective differential embedding. -/
theorem exists_ordinaryPoint_rationalMatrix [Infinite K]
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) :
    ∃ T : Polynomial K, T ≠ 0 ∧
      ∃ U : Matrix (Fin r) (Fin r) (Polynomial K),
        (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
          algebraMap (Polynomial K) (RatFunc K) T * A i j) ∧
        ∃ β : K, T.eval β ≠ 0 ∧
          ∃ B : Matrix (Fin r) (Fin r) (PowerSeries K),
            (∀ i j, B i j = ordinaryPointPolynomialSeries β (U i j) *
              (ordinaryPointPolynomialSeries β T)⁻¹) ∧
            (∀ i j, HahnSeries.ofPowerSeries ℤ K (B i j) =
              ordinaryPointRationalMap β (A i j)) := by
  classical
  obtain ⟨T, hT⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial K)) (fun ij : Fin r × Fin r => A ij.1 ij.2)
  choose U hU using hT
  have hTne : (T : Polynomial K) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp T.property
  have hclear (i j : Fin r) :
      algebraMap (Polynomial K) (RatFunc K) (U (i,j)) =
        algebraMap (Polynomial K) (RatFunc K) (T : Polynomial K) * A i j := by
    simpa only [Algebra.smul_def] using hU (i,j)
  obtain ⟨β, hβ⟩ := exists_ordinaryPoint_avoiding (T : Polynomial K) hTne
  refine ⟨(T : Polynomial K), hTne, Matrix.of (fun i j => U (i,j)), hclear,
    β, hβ, Matrix.of (fun i j => ordinaryPointPolynomialSeries β (U (i,j)) *
      (ordinaryPointPolynomialSeries β (T : Polynomial K))⁻¹), ?_, ?_⟩
  · intro i j
    rfl
  · intro i j
    exact (ordinaryPointRationalMap_of_clearing β (A i j)
      (T : Polynomial K) (U (i,j)) hβ (hclear i j)).symm

/-- Formal ordinary-point reduction for an arbitrary rational matrix in
characteristic zero, retaining the SAME rational entries and common denominator.
The equation is W'=B W with genuine matrix multiplication, not pointwise products. -/
theorem exists_ordinaryPoint_formalFundamentalMatrix [CharZero K]
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) :
    ∃ T : Polynomial K, T ≠ 0 ∧
      ∃ U : Matrix (Fin r) (Fin r) (Polynomial K),
        (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
          algebraMap (Polynomial K) (RatFunc K) T * A i j) ∧
        ∃ β : K, T.eval β ≠ 0 ∧
          ∃ B W : Matrix (Fin r) (Fin r) (PowerSeries K),
            (∀ i j, HahnSeries.ofPowerSeries ℤ K (B i j) =
              ordinaryPointRationalMap β (A i j)) ∧
            W.map (PowerSeries.constantCoeff K) = 1 ∧
            W.map (PowerSeries.derivative K) = B * W ∧ IsUnit W := by
  letI : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  obtain ⟨T, hT, U, hU, β, hβ, B, hBdef, hB⟩ :=
    exists_ordinaryPoint_rationalMatrix A
  obtain ⟨W, hW0, hWder, hWunit⟩ := exists_normalized_formal_fundamentalMatrix B
  exact ⟨T, hT, U, hU, β, hβ, B, W, hB, hW0, hWder, hWunit⟩

end StrictEUnit
end
