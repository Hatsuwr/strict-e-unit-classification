import OrdinaryPointFundamentalCoefficients
import OrdinaryPointConnectionDenominators
import SelectedRegularCompanionData

noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A constructed normalized unit fundamental matrix of the SAME rational
connection at a constructed integer ordinary point of the SAME clearing data.
Only common coefficient denominators are asserted, not conjugate house bounds. -/
def SameClearingOrdinaryFundamentalData {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  ∃ a : ℕ, t.eval (a:K) ≠ 0 ∧
    let B := ordinaryPointClearedMatrix t U (a:K)
    let Z := formalFundamentalMatrix B
    let v := T.eval (a : 𝓞 K)
    let q := Int.natAbs (Algebra.norm ℤ v)
    (∀ i j, HahnSeries.ofPowerSeries ℤ K (B i j) =
      ordinaryPointRationalMap (a:K) (A i j)) ∧
    Z.map (PowerSeries.constantCoeff K) = 1 ∧
    Z.map (PowerSeries.derivative K) = B * Z ∧ IsUnit Z ∧
    (∀ m i j, PowerSeries.coeff K m (Z i j) =
      (dividedPolynomialConnectionSequence t U m i j).eval (a:K) /
        (t.eval (a:K))^m) ∧
    0 < q ∧ 1 ≤ (q:ℝ)*E ∧
    ∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r,
        IsIntegral ℤ ((d:K) * PowerSeries.coeff K m (Z i j))

theorem same_integral_clearing_ordinary_fundamental_denominators {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K)) =
        algebraMap (Polynomial K) (RatFunc K)
          (T.map (algebraMap (𝓞 K) K)) * A i j)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ, ∃ δ : ℕ, 0 < δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K)))
          m i j).coeff l)) :
    SameClearingOrdinaryFundamentalData A T UI E := by
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  obtain ⟨a,ha,hq,hqE,hdena⟩ :=
    same_integral_clearing_ordinary_point_denominators T UI hT E hE hden
  let B := ordinaryPointClearedMatrix t U (a:K)
  let Z := formalFundamentalMatrix B
  refine ⟨a,ha,?_,formalFundamentalMatrix_constantCoeff B,
    formalFundamentalMatrix_derivative B,formalFundamentalMatrix_isUnit B,
    ?_,hq,hqE,?_⟩
  · intro i j
    exact (ordinaryPointRationalMap_of_clearing (a:K) (A i j)
      t (U i j) ha (hclear i j)).symm
  · intro m i j
    exact ordinaryPoint_fundamental_coeff t U (a:K) ha m i j
  · intro s
    obtain ⟨d,hd,hdb,hdi⟩ := hdena s
    refine ⟨d,hd,hdb,?_⟩
    intro m hm i j
    rw [ordinaryPoint_fundamental_coeff t U (a:K) ha m i j]
    simpa only [mul_div_assoc] using hdi m hm i j

theorem selectedRegularCompanionData_fundamental_denominators
    {L : Type*} [Field L]
    (G : PowerSeries K) (H : PowerSeries L) (φ : K →+* L)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (hpacket : SelectedRegularCompanionData G H φ r hr c T UI E) :
    SameClearingOrdinaryFundamentalData (minimalDerivativeCompanion r c) T UI E := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,hpEq⟩ := hpacket
  exact same_integral_clearing_ordinary_fundamental_denominators
    (minimalDerivativeCompanion r c) T UI hT hclear E hE hden

end StrictEUnit
end
