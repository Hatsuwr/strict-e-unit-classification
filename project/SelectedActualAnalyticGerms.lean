import OrdinaryActualScalarGerms
import ArbitraryOrdinaryAnalyticGerms

noncomputable section
open scoped Topology BigOperators NumberField Matrix
namespace StrictEUnit

/-- Actual independent scalar germs, with the literal Taylor coefficients
and original operator, at a fixed ordinary point. -/
def ActualCompanionScalarGermsAt
    {K : Type*} [Field K] [NumberField K]
    (r : ℕ) (hr : 0 < r) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) (σ : K →+* ℂ) : Prop :=
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  let g : Fin r → ℂ → ℂ := fun j z =>
    ordinaryPointAnalyticMatrix σ t U α ⟨0,hr⟩ j (z-σ α)
  let q := sameCompanionScalarTuple r hr t U
  ∃ C : ℝ, ∃ hC : 1 ≤ C,
    (∀ j, HasFPowerSeriesOnBall (g j)
      (FormalMultilinearSeries.ofScalars ℂ
        (fun n => σ (PowerSeries.coeff K n (Z ⟨0,hr⟩ j))))
      (σ α) (ordinaryGermRadius C hC : ENNReal)) ∧
    IndependentAnalyticGermsAt (σ α) g ∧
    ∀ᶠ z in nhds (σ α), ∀ j,
      (∑ i, ((q i).map σ).eval z * iteratedDeriv i.val (g j) z)=0

variable {K : Type*} [Field K] [NumberField K]

/-- One and the same integer ordinary point carries the retained arithmetic
packet, translated formal family, and actual complex analytic germs. -/
def SameClearingActualAnalyticGermsData
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (χ : K →+* AlgebraicComplex) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  ∃ a : ℕ, t.eval (a:K) ≠ 0 ∧
    let B := ordinaryPointClearedMatrix t U (a:K)
    let Z := formalFundamentalMatrix B
    let v := T.eval (a : 𝓞 K)
    let q := Int.natAbs (Algebra.norm ℤ v)
    (∀ i j, HahnSeries.ofPowerSeries ℤ K (B i j) =
      ordinaryPointRationalMap (a:K) (minimalDerivativeCompanion r c i j)) ∧
    Z.map (PowerSeries.constantCoeff K) = 1 ∧
    Z.map (PowerSeries.derivative K) = B * Z ∧ IsUnit Z ∧
    (∀ m i j, PowerSeries.coeff K m (Z i j) =
      (dividedPolynomialConnectionSequence t U m i j).eval (a:K) /
        (t.eval (a:K))^m) ∧
    0 < q ∧ 1 ≤ (q:ℝ)*E ∧
    (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r,
        IsIntegral ℤ ((d:K) * PowerSeries.coeff K m (Z i j))) ∧
    HasJointStrictEArithmeticMatrix Z χ ∧
    TranslatedCompanionScalarFamilyAt r hr t U (a:K) χ ∧
    ∀ σ : K →+* ℂ, ActualCompanionScalarGermsAt r hr t U (a:K) σ


theorem sameClearingTranslatedScalarFamilyData_actual_analytic_germs
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (χ : K →+* AlgebraicComplex)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K)) =
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K)) *
          minimalDerivativeCompanion r c i j)
    (hpacket : SameClearingTranslatedScalarFamilyData r hr c T UI E χ) :
    SameClearingActualAnalyticGermsData r hr c T UI E χ := by
  obtain ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden,hjoint,hscalar⟩ := hpacket
  refine ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden,hjoint,hscalar,?_⟩
  intro σ
  exact ordinaryPoint_actual_scalar_germs r hr c _ _ hclear (a:K) ha σ

end StrictEUnit
end
