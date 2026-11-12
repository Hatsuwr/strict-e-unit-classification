import OrdinaryPointScalarIndependence

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- The full translated ordinary scalar family at ONE fixed point, including
jet normalization, independence over each coefficient field, and equations
for the literal polynomial translation of the SAME selected tuple. -/
def TranslatedCompanionScalarFamilyAt
    {K L : Type*} [Field K] [Field L]
    (r : ℕ) (hr : 0 < r) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) (χ : K →+* L) : Prop :=
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  let f : Fin r → PowerSeries K := fun j => Z ⟨0,hr⟩ j
  let g : Fin r → PowerSeries L := fun j => PowerSeries.map χ (f j)
  let q := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial K := fun i => (q i).comp (Polynomial.X + Polynomial.C α)
  (∀ i j : Fin r, PowerSeries.constantCoeff K
    ((PowerSeries.derivative K)^[i.val] (f j)) = if i=j then 1 else 0) ∧
  LinearIndependent K f ∧ LinearIndependent L g ∧
  (∀ j, (∑ i, (p i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] (f j)) = 0) ∧
  (∀ j, (∑ i, ((p i).map χ : PowerSeries L) * (PowerSeries.derivative L)^[i.val] (g j)) = 0)

theorem ordinaryPoint_companion_translated_scalar_family
    {K L : Type*} [Field K] [CharZero K] [Field L]
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) t * minimalDerivativeCompanion r c i l)
    (α : K) (hα : t.eval α ≠ 0) (χ : K →+* L) :
    TranslatedCompanionScalarFamilyAt r hr t U α χ := by
  cases r with
  | zero => omega
  | succ n =>
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact ordinaryPoint_companion_first_row_jet_values n c t U hclear α hα
    · exact ordinaryPoint_companion_first_row_linearIndependent n c t U hclear α hα
    · exact ordinaryPoint_companion_first_row_map_linearIndependent χ n c t U hclear α hα
    · exact ordinaryPoint_companion_first_row_scalar n c t U hclear α hα
    · intro j
      exact ordinaryTuple_equation_map χ (n+1)
        (fun i => (sameCompanionScalarTuple (n+1) hr t U i).comp
          (Polynomial.X + Polynomial.C α)) _
        (ordinaryPoint_companion_first_row_scalar n c t U hclear α hα j)

variable {K : Type*} [Field K] [NumberField K]

/-- All prior SAME-point arithmetic packet fields, now with the actual
independent translated scalar family attached at that very point. -/
def SameClearingTranslatedScalarFamilyData
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
    TranslatedCompanionScalarFamilyAt r hr t U (a:K) χ

theorem sameClearingOrdinaryArithmeticData_translated_scalar_family
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (χ : K →+* AlgebraicComplex)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K)) =
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K)) *
          minimalDerivativeCompanion r c i j)
    (hpacket : SameClearingOrdinaryArithmeticData (minimalDerivativeCompanion r c) T UI E χ) :
    SameClearingTranslatedScalarFamilyData r hr c T UI E χ := by
  obtain ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden,hjoint⟩ := hpacket
  refine ⟨a,ha,hB,hZ0,hZder,hZunit,hcoeff,hq,hqE,hden,hjoint,?_⟩
  exact ordinaryPoint_companion_translated_scalar_family r hr c _ _ hclear (a:K) ha χ

theorem selectedRegularCompanionData_translated_scalar_family
    {L : Type*} [Field L]
    (G : PowerSeries K) (H : PowerSeries L) (φ : K →+* L)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (χ : K →+* AlgebraicComplex)
    (hpacket : SelectedRegularCompanionData G H φ r hr c T UI E) :
    SameClearingTranslatedScalarFamilyData r hr c T UI E χ := by
  exact sameClearingOrdinaryArithmeticData_translated_scalar_family r hr c T UI E χ
    hpacket.2.2.1
    (selectedRegularCompanionData_joint_arithmetic G H φ r hr c T UI E χ hpacket)

end StrictEUnit
end
