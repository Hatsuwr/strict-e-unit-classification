import SelectedRegularCompanionData
import OrdinaryReflectionValuation
import ValuedReciprocalFourier
import Stage53FourierTupleNonzero

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- Exact full selected-source conclusion, packaged over a generic source field.
Source order r and Fourier order ν remain separate. -/
def SelectedFuchsSourceData
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ) : Prop :=
      let t := T.map (algebraMap (𝓞 K) K)
      let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
        Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
      let qF := sameCompanionScalarTuple r hr t U
      let p : Fin (r+1) → Polynomial AlgebraicComplex :=
        fun i => (qF i).map (φ)
      let qplus := ordinaryReflectionTuple r p
      let d := reciprocalCommonDegree r qplus
      let ν := reciprocalSourceDegree r d qplus
      let A := reciprocalSourceArray r d qplus
      OrdinaryBorelArithmeticConnectionData G r c ∧
      t ≠ 0 ∧
      (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) t * minimalDerivativeCompanion r c i j) ∧
      qF (Fin.last r) = t ∧ qF (Fin.last r) ≠ 0 ∧
      (∑ i : Fin (r+1), selectedLaurentRationalAct
        (algebraMap (Polynomial K) (RatFunc K) (qF i))
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
      ReciprocalRegularSingularBounds r qF ∧
      p (Fin.last r) ≠ 0 ∧ ReciprocalRegularSingularBounds r p ∧
      qplus (Fin.last r) ≠ 0 ∧ ReciprocalRegularSingularBounds r qplus ∧
      ν = d - (qplus (Fin.last r)).natTrailingDegree + 2*r+1 ∧
      0 < ν ∧ Stage56FiniteFuchs A ∧ A (Fin.last r) (Fin.last ν) ≠ 0 ∧
      signedLaplaceSourceAction A
        (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
          HahnSeries.ofPowerSeries ℤ AlgebraicComplex
            (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n)) = 0 ∧
      (∃ l : Fin (ν+1), stage53_fourierCoeff A l ≠ 0) ∧
      (∑ l, (stage53_fourierCoeff A l : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[l.val]
          (stage41_strictFormalSeries a)) = 0

theorem selectedRegularCompanionData_fuchs_source
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (hpacket : SelectedRegularCompanionData G (PowerSeries.mk a) φ r hr c T UI E) :
    SelectedFuchsSourceData G a φ r hr c T UI E := by
  rcases hpacket with ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,hpEq⟩
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let qF := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial AlgebraicComplex := fun i => (qF i).map φ
  let qplus := ordinaryReflectionTuple r p
  have hplus : qplus (Fin.last r) ≠ 0 ∧ ReciprocalRegularSingularBounds r qplus :=
    (ordinaryReflectionTuple_last_and_valuation_iff r p).2 ⟨hpTop,hpReg⟩
  have heq := ordinaryReflectionTuple_signed_mk a r p hpEq
  have hv := valued_signed_ordinary_original_factorial r qplus hplus.1 hplus.2 a heq
  have hd := reciprocalSourceDegree_of_valuations r qplus hplus.1 hplus.2
  refine ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplus.1,hplus.2,hd,hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,?_,hv.2.2.2.2⟩
  exact stage53_fourierCoeff_exists_ne_zero _ ⟨Fin.last r,Fin.last _,hv.2.2.1⟩

end StrictEUnit
end
