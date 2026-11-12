import TypeIIDividedColumnIntegral
import TypeIIDualColumnAttachment
import IntegralCommonDualMatrix

/-! A single finite-prefix multiplier and a single chosen integral column
family supply the SAME common matrix. No determinant/rank premise is hidden. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Divided dual iteration respects one coherent constant-field rescaling. -/
theorem dualDividedColumn_smul_seed
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (D : Module.End k V) (P : V) (δ : k) (j : ℕ) :
    dualDividedColumn D (δ • P) j = δ • dualDividedColumn D P j := by
  simp only [dualDividedColumn, map_smul, smul_smul]
  rw [mul_comm]

/-- Exact ring map for an integral coefficient ring inside K and then K(z). -/
def typeIIRationalPolynomialMap {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) : Polynomial R →+* RatFunc K :=
  (algebraMap (Polynomial K) (RatFunc K)).comp (Polynomial.mapRingHom φ)

theorem typeIIRationalPolynomialMap_derivative
    {R K : Type*} [CommRing R] [Field K]
    (φ : R →+* K) (p : Polynomial R) :
    stage14_rationalOrdinaryDerivation (typeIIRationalPolynomialMap φ p) =
      typeIIRationalPolynomialMap φ p.derivative := by
  change stage14_rationalOrdinaryDerivation
    (algebraMap (Polynomial K) (RatFunc K) (p.map φ)) =
      algebraMap (Polynomial K) (RatFunc K) (p.derivative.map φ)
  rw [stage14_rationalOrdinaryDerivation_polynomial, Polynomial.derivative_map]

/-- The supplied Type-II approximation, clearing and finite arithmetic prefix
CONSTRUCT one integral column family. Its first r columns form one common
matrix for all n≤s. The representatives are not supplied as a hypothesis. -/
theorem exists_typeII_common_integral_matrix
    {R K : Type*} [CommRing R] [Field K] [CharZero K] {r : ℕ}
    (φ : R →+* K) (T Q : Polynomial R)
    (U : Fin r → Fin r → Polynomial K) (P : Fin r → Polynomial K)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → R) (δ : K)
    (N M τ s : ℕ)
    (hT0 : typeIIRationalPolynomialMap φ T ≠ 0)
    (hT : (T.map φ).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap φ T * A i l)
    (hf : ∀ i, (T.map φ : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map φ : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → φ (b i n) = δ * PowerSeries.coeff K n (f i))
    (hcut : (s+r-1)*(τ+1) ≤ M) :
    ∃ Z : ℕ → Fin r → Polynomial R,
      (∀ j, j ≤ s+r-1 → ∀ i, (Z j i).map φ = Polynomial.C δ *
        typeIIDividedColumn (T.map φ) U P j i) ∧
      (∀ j, j ≤ s+r-1 → ∀ i,
        typeIIRationalPolynomialMap φ (Z j i) =
          (typeIIRationalPolynomialMap φ T)^j *
            dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
              (δ • (fun l => algebraMap (Polynomial K) (RatFunc K) (P l))) j i) ∧
      (∀ n, n ≤ s → ∃ B : Matrix (Fin r) (Fin r) (Polynomial R),
        Matrix.of (fun i l : Fin r => (typeIIRationalPolynomialMap φ T)^n *
          matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i l /
            (n.factorial : RatFunc K)) *
          Matrix.of (fun l j : Fin r => typeIIRationalPolynomialMap φ (Z j.val l)) =
            B.map (typeIIRationalPolynomialMap φ)) := by
  classical
  letI : CharZero (RatFunc K) := ⟨by
    intro m n h
    apply Nat.cast_injective (R := K)
    apply (algebraMap K (RatFunc K)).injective
    simpa only [map_natCast] using h⟩
  obtain ⟨Z, hZ⟩ := typeII_simultaneous_divided_column_integral φ T Q U P f b δ
    N M τ (s+r-1) hT hU hP hf hcontact hb hcut
  have hdual (j : ℕ) (hj : j ≤ s+r-1) (i : Fin r) :
      typeIIRationalPolynomialMap φ (Z j i) =
        (typeIIRationalPolynomialMap φ T)^j *
          dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
            (δ • (fun l => algebraMap (Polynomial K) (RatFunc K) (P l))) j i := by
    change algebraMap (Polynomial K) (RatFunc K) ((Z j i).map φ) = _
    rw [hZ j hj i, map_mul,
      typeIIDividedColumn_ratFunc_dual (T.map φ) U P A hclear j i,
      dualDividedColumn_smul_seed]
    simp only [Pi.smul_apply, Algebra.smul_def, RatFunc.algebraMap_C,
      RatFunc.algebraMap_eq_C]
    rw [show typeIIRationalPolynomialMap φ T =
      algebraMap (Polynomial K) (RatFunc K) (T.map φ) from rfl]
    ring
  refine ⟨Z, hZ, hdual, ?_⟩
  exact exists_common_dual_matrix_polynomial_products
    (typeIIRationalPolynomialMap φ) stage14_rationalOrdinaryDerivation
    (typeIIRationalPolynomialMap_derivative φ) T hT0 A
    (δ • (fun l => algebraMap (Polynomial K) (RatFunc K) (P l))) Z s hdual

end StrictEUnit
end
