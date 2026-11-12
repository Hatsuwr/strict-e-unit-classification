import ActualMinimalArithmeticConnection
import SameCompanionScalarTuple

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- Positive true order and minimality belong to this selected tuple, not to
an arbitrary original Stage41 annihilator. Scalars act on the original Laurent G. -/
theorem sameCompanionScalarTuple_spec
    {K : Type*} [Field K] [CharZero K] (G : LaurentSeries K)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData G r c)
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion r c i j) :
    sameCompanionScalarTuple r hr T U (Fin.last r) = T ∧
    sameCompanionScalarTuple r hr T U (Fin.last r) ≠ 0 ∧
    (∑ i : Fin (r+1), algebraMap (Polynomial K) (RatFunc K)
      (sameCompanionScalarTuple r hr T U i) •
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) = 0 ∧
    (∀ a : Fin r → RatFunc K,
      (∑ i, a i • (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) = 0 →
      ∀ i, a i = 0) := by
  classical
  have hlast : sameCompanionScalarTuple r hr T U (Fin.last r) = T := by
    simp [sameCompanionScalarTuple]
  have hrow (i : Fin r) : algebraMap (Polynomial K) (RatFunc K)
      (U ⟨r-1, by omega⟩ i) = algebraMap (Polynomial K) (RatFunc K) T * c i := by
    have h := hclear ⟨r-1, by omega⟩ i
    simpa only [minimalDerivativeCompanion, show ¬ (r-1)+1 < r by omega, if_false] using h
  refine ⟨hlast,by rw [hlast]; exact hT,?_,?_⟩
  · rw [Fin.sum_univ_castSucc]
    simp only [sameCompanionScalarTuple, Fin.lastCases_castSucc, Fin.lastCases_last,
      Fin.coe_castSucc, Fin.val_last, map_neg, neg_smul]
    simp_rw [hrow, mul_smul]
    rw [Finset.sum_neg_distrib, ← Finset.smul_sum, hdata.2.1]
    exact neg_add_cancel _
  · intro a ha
    exact Fintype.linearIndependent_iff.mp hdata.1 a ha

/-- Extract once from the arithmetic package. The exact integral clearing and
its exponential common-denominator certificate remain in the conclusion. -/
theorem ordinaryBorelArithmeticConnection_scalar_selection
    {K : Type*} [Field K] [NumberField K] (G : PowerSeries K)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (hdata : OrdinaryBorelArithmeticConnectionData G r c) :
    ∃ T : Polynomial (𝓞 K), ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)),
      let t := T.map (algebraMap (𝓞 K) K)
      let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
        Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
      let q := sameCompanionScalarTuple r hr t U
      t ≠ 0 ∧
      (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) t * minimalDerivativeCompanion r c i j) ∧
      q (Fin.last r) = t ∧ q (Fin.last r) ≠ 0 ∧
      (∑ i : Fin (r+1), algebraMap (Polynomial K) (RatFunc K) (q i) •
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (HahnSeries.ofPowerSeries ℤ K G)) = 0 ∧
      (∀ a : Fin r → RatFunc K,
        (∑ i, a i • (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (HahnSeries.ofPowerSeries ℤ K G)) = 0 → ∀ i, a i = 0) ∧
      ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ E^(s+1) ∧
        ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
          IsIntegral ℤ ((d:K)*(dividedPolynomialConnectionSequence t U n i j).coeff l) := by
  obtain ⟨hminimal,T,UI,hT,hclear,E,hE,hbound⟩ := hdata
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  obtain ⟨htop,hnonzero,hann,hmin⟩ := sameCompanionScalarTuple_spec
    (HahnSeries.ofPowerSeries ℤ K G) r hr c hminimal
    (T.map (algebraMap (𝓞 K) K)) U hT hclear
  exact ⟨T,UI,hT,hclear,htop,hnonzero,hann,hmin,E,hE,hbound⟩

end StrictEUnit
end
