import TypeIICommonIntegralMatrix
import TypeIIIntegralLiftIdentity
import TypeIIIntegralLiftDeterminant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Nonzero independent column scalings force the ORIGINAL matrix determinant
nonzero. No injectivity premise on the ring map is required for reflection. -/
theorem mapped_scaled_columns_det_ne_zero
    {R B : Type*} [CommRing R] [Field B] {r : ℕ}
    (φ : R →+* B) (M : Matrix (Fin r) (Fin r) R)
    (Y : Fin r → Fin r → B) (a : Fin r → B)
    (hli : LinearIndependent B Y) (ha : ∀ j, a j ≠ 0)
    (hcol : ∀ i j, φ (M i j) = a j*Y j i) : M.det ≠ 0 := by
  classical
  have hscaled : LinearIndependent B (fun j => a j • Y j) := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc
    simp only [smul_smul] at hc
    have hz := Fintype.linearIndependent_iff.mp hli (fun j => c j*a j) hc
    intro j
    exact (mul_eq_zero.mp (hz j)).resolve_right (ha j)
  have hcolumns : (φ.mapMatrix M).col = fun j => a j • Y j := by
    funext j i
    exact hcol i j
  have hu : IsUnit (φ.mapMatrix M) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp (by rw [hcolumns]; exact hscaled)
  have hd : (φ.mapMatrix M).det ≠ 0 :=
    (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero
  intro hz
  apply hd
  rw [← φ.map_det, hz, map_zero]

/-- The first r columns of the SAME literal integral lift have nonzero
polynomial determinant and a nonzero coefficient. The only rank input is
independence of the SAME P's divided dual columns. Positive delta and nonzero
T supply exactly the nonzero column scalars; no unit value T(0) is needed. -/
theorem typeII_literal_lift_det_and_coefficient_ne_zero
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T Q : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → 𝓞 K) (δ : ℕ) (hδ : 0 < δ)
    (N M τ : ℕ)
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → (b i n : K) = (δ:K)*PowerSeries.coeff K n (f i))
    (hcut : (r-1)*(τ+1) ≤ M)
    (hli : LinearIndependent (RatFunc K) (fun j : Fin r =>
      dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
        (fun i => algebraMap (Polynomial K) (RatFunc K) (P i)) j.val)) :
    (typeIIIntegralLiftMatrix r N τ T Q b).det ≠ 0 ∧
      ∃ k, (typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k ≠ 0 := by
  classical
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let ψ : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  let ι := typeIIRationalPolynomialMap φ
  let Y := fun j : Fin r =>
    dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
      (fun i => ψ (P i)) j.val
  let a := fun j : Fin r => ψ (Polynomial.C (δ:K))*(ι T)^j.val
  have hδK : (δ:K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hδ)
  have hδP : Polynomial.C (δ:K) ≠ 0 := by
    intro hz
    exact hδK (Polynomial.C_injective (hz.trans (map_zero Polynomial.C).symm))
  have hδB : ψ (Polynomial.C (δ:K)) ≠ 0 := by
    intro hz
    exact hδP (RatFunc.algebraMap_injective (K:=K) (hz.trans (map_zero ψ).symm))
  have ha (j : Fin r) : a j ≠ 0 := mul_ne_zero hδB (pow_ne_zero _ hT0)
  have he (i j : Fin r) : ι (typeIIIntegralLiftMatrix r N τ T Q b i j) = a j*Y j i := by
    have hj : j.val*(τ+1) ≤ M :=
      (Nat.mul_le_mul_right (τ+1) (show j.val ≤ r-1 by omega)).trans hcut
    have hmap := typeIIIntegralLift_map_column φ T Q U P f b (δ:K) N M τ j.val
      hT hU hP hf hcontact hb hj i
    change ψ ((typeIIIntegralLift T Q (b i) (N+j.val*τ) j.val).map φ) = _
    rw [hmap, map_mul,
      typeIIDividedColumn_ratFunc_dual (T.map φ) U P A hclear j.val i]
    change ψ (Polynomial.C (δ:K))*((ι T)^j.val*Y j i) =
      (ψ (Polynomial.C (δ:K))*(ι T)^j.val)*Y j i
    ring
  have hd := mapped_scaled_columns_det_ne_zero ι (typeIIIntegralLiftMatrix r N τ T Q b)
    Y a hli ha he
  refine ⟨hd, ?_⟩
  by_contra hn
  push_neg at hn
  apply hd
  apply Polynomial.ext
  intro k
  simpa only [Polynomial.coeff_zero] using hn k

end StrictEUnit
end
