import OrdinaryPointHouseGrowth
import OrdinaryPointFundamentalArithmetic

noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- ONE constant and ONE cutoff-denominator sequence for every raw coefficient
of a finite matrix. The factorial series of these raw sequences is a separate
inverse-Borel object; the ordinary matrix itself is not declared strict-E. -/
def HasJointStrictEArithmeticMatrix {r : ℕ}
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (φ : K →+* AlgebraicComplex) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧
    (∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n i j,
      ‖σ (φ (PowerSeries.coeff K n (Z i j)))‖ ≤ C^(n+1)) ∧
    ∃ d : ℕ → ℕ, (∀ n, 0 < d n) ∧ (∀ n, (d n : ℝ) ≤ C^(n+1)) ∧
      ∀ n m, m ≤ n → ∀ i j,
        IsIntegral ℤ ((d n : ℂ) * (φ (PowerSeries.coeff K m (Z i j)) : ℂ))

theorem jointStrictEArithmeticMatrix_entry {r : ℕ}
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K)) (φ : K →+* AlgebraicComplex)
    (h : HasJointStrictEArithmeticMatrix Z φ) (i j : Fin r) :
    HasStrictEArithmetic (fun n => φ (PowerSeries.coeff K n (Z i j))) := by
  obtain ⟨C,hC,hbound,d,hd,hdb,hint⟩ := h
  exact ⟨C,hC,(fun σ n => hbound σ n i j),d,hd,hdb,
    fun n m hm => hint n m hm i j⟩

/-- Combine derived house bounds and existing common denominators without
adding a desired arithmetic-family premise. -/
theorem jointStrictEArithmeticMatrix_of_house_and_denominators {r : ℕ}
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K)) (φ : K →+* AlgebraicComplex)
    (C0 : ℝ) (hC0 : 1 ≤ C0)
    (hhouse : ∀ n i j, NumberField.house (PowerSeries.coeff K n (Z i j)) ≤ C0^n)
    (Q : ℝ) (hQ : 1 ≤ Q)
    (hden : ∀ n, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ Q^(n+1) ∧
      ∀ m, m ≤ n → ∀ i j, IsIntegral ℤ ((d:K)*PowerSeries.coeff K m (Z i j))) :
    HasJointStrictEArithmeticMatrix Z φ := by
  classical
  choose d hd hdb hint using hden
  let C := max C0 Q
  have hC : 1 ≤ C := hC0.trans (le_max_left _ _)
  refine ⟨C,hC,?_,d,hd,?_,?_⟩
  · intro σ n i j
    calc
      _ ≤ NumberField.house (PowerSeries.coeff K n (Z i j)) :=
        conjugate_norm_le_house (σ.toRingHom.comp φ) _
      _ ≤ C0^n := hhouse n i j
      _ ≤ C^n := pow_le_pow_left₀ (le_trans zero_le_one hC0) (le_max_left _ _) n
      _ ≤ C^(n+1) := pow_le_pow_right₀ hC (Nat.le_succ n)
  · intro n
    exact (hdb n).trans (pow_le_pow_left₀ (le_trans zero_le_one hQ) (le_max_right _ _) _)
  · intro n m hm i j
    let ψ : K →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom.comp φ
    have hh := IsIntegral.map ψ.toIntAlgHom (hint n m hm i j)
    simpa only [RingHom.toIntAlgHom_apply, map_mul, map_natCast, ψ,
      RingHom.comp_apply] using hh

/-- The old packet is retained at exactly its already selected point, now
with joint raw-coefficient arithmetic attached. -/
def SameClearingOrdinaryArithmeticData {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (φ : K →+* AlgebraicComplex) : Prop :=
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
    (∀ s : ℕ, ∃ d : ℕ, 0 < d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
      ∀ m, m ≤ s → ∀ i j : Fin r,
        IsIntegral ℤ ((d:K) * PowerSeries.coeff K m (Z i j))) ∧
    HasJointStrictEArithmeticMatrix Z φ

theorem sameClearingOrdinaryFundamentalData_joint_arithmetic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (φ : K →+* AlgebraicComplex)
    (hpacket : SameClearingOrdinaryFundamentalData A T UI E) :
    SameClearingOrdinaryArithmeticData A T UI E φ := by
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  obtain ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden⟩ := hpacket
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U (a:K))
  obtain ⟨C0,hC0,hhouse⟩ := ordinaryPoint_fundamental_house_bound t U (a:K) ha
  refine ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden,?_⟩
  exact jointStrictEArithmeticMatrix_of_house_and_denominators Z φ C0 hC0 hhouse _ hqE hden

theorem selectedRegularCompanionData_joint_arithmetic
    {L : Type*} [Field L]
    (G : PowerSeries K) (H : PowerSeries L) (φ : K →+* L)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (χ : K →+* AlgebraicComplex)
    (hpacket : SelectedRegularCompanionData G H φ r hr c T UI E) :
    SameClearingOrdinaryArithmeticData (minimalDerivativeCompanion r c) T UI E χ := by
  exact sameClearingOrdinaryFundamentalData_joint_arithmetic
    (minimalDerivativeCompanion r c) T UI E χ
    (selectedRegularCompanionData_fundamental_denominators G H φ r hr c T UI E hpacket)

end StrictEUnit
end
