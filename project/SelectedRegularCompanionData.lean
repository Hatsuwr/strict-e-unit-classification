import ActualCompanionLocalRegularity
import SelectedScalarPowerSeriesTransport
import SelectedScalarFieldMapTransport
import SelectedScalarLaurentAction

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- The full unchanged conjunction for the SAME selected arithmetic companion.
This definition only packages the conclusion to keep concrete-field elaboration bounded. -/
def SelectedRegularCompanionData
    {K L : Type*} [Field K] [NumberField K] [Field L]
    (G : PowerSeries K) (H : PowerSeries L) (φ : K →+* L)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let q := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial L := fun i => (q i).map φ
  OrdinaryBorelArithmeticConnectionData G r c ∧
  t ≠ 0 ∧
  (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
    algebraMap (Polynomial K) (RatFunc K) t * minimalDerivativeCompanion r c i j) ∧
  q (Fin.last r) = t ∧ q (Fin.last r) ≠ 0 ∧
  (∑ i : Fin (r+1), selectedLaurentRationalAct
    (algebraMap (Polynomial K) (RatFunc K) (q i))
    ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
      (HahnSeries.ofPowerSeries ℤ K G))) = 0 ∧
  (∀ b : Fin r → RatFunc K,
    (∑ i, selectedLaurentRationalAct (b i)
      ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (HahnSeries.ofPowerSeries ℤ K G))) = 0 → ∀ i, b i = 0) ∧
  1 ≤ E ∧
  (∀ s : ℕ, ∃ δ : ℕ, 0 < δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
    ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
      IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence t U n i j).coeff l)) ∧
  ReciprocalRegularSingularBounds r q ∧
  p (Fin.last r) ≠ 0 ∧ ReciprocalRegularSingularBounds r p ∧
  (∑ i, (p i : PowerSeries L) * (PowerSeries.derivative L)^[i.val] H) = 0

theorem exists_selectedRegularCompanionData
    {K L : Type*} [Field K] [NumberField K] [Field L]
    (G : PowerSeries K) (H : PowerSeries L) (φ : K →+* L)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (hdata : OrdinaryBorelArithmeticConnectionData G r c)
    (hGH : PowerSeries.map φ G = H) :
    ∃ T : Polynomial (𝓞 K),
    ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)), ∃ E : ℝ,
      SelectedRegularCompanionData G H φ r hr c T UI E := by
  obtain ⟨T,UI,hT,hclear,htop,hqn,hann,hmin,hden,hreg⟩ :=
    ordinaryBorelArithmeticConnection_regular_scalar_selection G r hr c hdata
  obtain ⟨E,hE,hden⟩ := hden
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let q := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial L := fun i => (q i).map φ
  have hps := powerSeries_equation_of_laurent_scalar_equation G r q hann
  have hpTop : p (Fin.last r) ≠ 0 :=
    (Polynomial.map_ne_zero_iff φ.injective).2 hqn
  have hpReg : ReciprocalRegularSingularBounds r p :=
    reciprocalRegularSingularBounds_map φ r q hreg
  have hpEq : (∑ i, (p i : PowerSeries L) *
      (PowerSeries.derivative L)^[i.val] H) = 0 := by
    have hm := ordinaryTuple_equation_map φ r q G hps
    simpa only [hGH] using hm
  refine ⟨T,UI,E,?_⟩
  exact ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,hpEq⟩

end StrictEUnit
end
