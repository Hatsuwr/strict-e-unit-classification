import CompanionArithmeticLocalRegularity
import SameCompanionScalarSelection

/-! Source-only actual-package extraction. The original Stage41 polynomial
annihilator need not be minimal and is not claimed regular here. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- One extraction of the SAME arithmetic companion yields the selected
positive-order scalar tuple, its actual annihilation and minimality, the same
arithmetic certificate, and the derived regular-singular inequalities. -/
theorem ordinaryBorelArithmeticConnection_regular_scalar_selection
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
      (∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ E^(s+1) ∧
        ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
          IsIntegral ℤ ((d:K)*(dividedPolynomialConnectionSequence t U n i j).coeff l)) ∧
      ReciprocalRegularSingularBounds r q := by
  cases r with
  | zero => omega
  | succ n =>
    obtain ⟨T,UI,hT,hclear,htop,hqn,hann,hmin,E,hE,hden⟩ :=
      ordinaryBorelArithmeticConnection_scalar_selection G (n+1) hr c hdata
    refine ⟨T,UI,hT,hclear,htop,hqn,hann,hmin,⟨E,hE,hden⟩,?_⟩
    exact sameCompanionScalarTuple_regular_of_common_denominators n c
      (T.map (algebraMap (𝓞 K) K))
      (Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K)))
      hT hclear E hE hden

end StrictEUnit
end
