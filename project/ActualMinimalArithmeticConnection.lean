import MinimalCompanionPowerSeriesClearing
import OrdinaryDerivativePrefixArithmetic
import IntegralRationalMatrixClearing
import TypeIISystemExponential

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- Arithmetic small denominators for the SAME companion, retaining the exact
integral clearing and the original cyclic data. This is not regularity. -/
def OrdinaryBorelArithmeticConnectionData
    {K : Type*} [Field K] [NumberField K] (G : PowerSeries K)
    (r : ℕ) (c : Fin r → RatFunc K) : Prop :=
  OrdinaryBorelMinimalCyclicData (HahnSeries.ofPowerSeries ℤ K G) r c ∧
  ∃ T : Polynomial (𝓞 K), ∃ UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)),
    T.map (algebraMap (𝓞 K) K) ≠ 0 ∧
    (∀ i j, algebraMap (Polynomial K) (RatFunc K) ((UI i j).map (algebraMap (𝓞 K) K)) =
      algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
        minimalDerivativeCompanion r c i j) ∧
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ E^(s+1) ∧
      ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((q:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))) n i j).coeff l)

/-- Finite input bounds are chosen internally, not extra endpoint assumptions. -/
theorem integral_clearing_finite_bounds
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
    ∃ e τ : ℕ, ∃ HT : ℝ, 1 ≤ HT ∧ T.natDegree ≤ e ∧
      (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ ∧
      (∀ i j, (U i j).natDegree ≤ τ) ∧
      ∀ n, NumberField.house (T.coeff n : K) ≤ HT := by
  classical
  let τ := (T.map (algebraMap (𝓞 K) K)).natDegree +
    ∑ ij : Fin r × Fin r, (U ij.1 ij.2).natDegree
  let HT : ℝ := 1 + ∑ n ∈ T.support, NumberField.house (T.coeff n : K)
  have hsum : 0 ≤ ∑ n ∈ T.support, NumberField.house (T.coeff n : K) :=
    Finset.sum_nonneg (fun n _ => NumberField.house_nonneg _)
  refine ⟨T.natDegree,τ,HT,by dsimp [HT]; linarith,le_rfl,?_,?_,?_⟩
  · dsimp [τ]; omega
  · intro i j
    have h := Finset.single_le_sum (f:=fun ij : Fin r × Fin r => (U ij.1 ij.2).natDegree)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
    change (U i j).natDegree ≤ ∑ ij : Fin r × Fin r, (U ij.1 ij.2).natDegree at h
    dsimp [τ]; omega
  · intro n
    by_cases hn : n ∈ T.support
    · have h := Finset.single_le_sum (f:=fun n => NumberField.house (T.coeff n : K))
        (fun _ _ => NumberField.house_nonneg _) hn
      dsimp [HT]; linarith
    · have hz : T.coeff n = 0 := Polynomial.not_mem_support_iff.mp hn
      rw [hz]
      change NumberField.house (0:K) ≤ HT
      simpa only [NumberField.house, map_zero, norm_zero] using
        (zero_le_one.trans (show 1 ≤ HT by dsimp [HT]; linarith))

/-- The original arithmetic certificate is destructured once. Its shift
δ₁(L)=δ₀(L+r) and exact integral prefix are used for the SAME original G. -/
theorem ordinaryBorelMinimalCyclic_arithmetic_connection
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    (a : ℕ → AlgebraicComplex) (ha : HasStrictEArithmetic a)
    (hmem : ∀ n, a n ∈ F) (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc F)
    (hdata : OrdinaryBorelMinimalCyclicData
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) r c) :
    OrdinaryBorelArithmeticConnectionData
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) r c := by
  classical
  let A := minimalDerivativeCompanion r c
  obtain ⟨T0,hT0,U0,hclear0,z,hz,T,UI,hmapT,hmapU,hT,hTmap,hclear⟩ :=
    exists_integral_polynomial_matrix_clearing F r A
  let φ : 𝓞 F →+* F := algebraMap (𝓞 F) F
  let U : Matrix (Fin r) (Fin r) (Polynomial F) := Matrix.of (fun i j => (UI i j).map φ)
  let G := PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)
  let f := ordinaryDerivativePrefix r G
  obtain ⟨hli,hf⟩ := minimal_companion_powerSeries_clearing G r c hdata (T.map φ) U hclear
  have hT0' : typeIIRationalPolynomialMap φ T ≠ 0 := by
    intro h
    apply hTmap
    apply RatFunc.algebraMap_injective (K:=F)
    simpa only [map_zero] using h
  obtain ⟨e,τ,HT,hHT,hTe,hTτ,hUτ,hTH⟩ := integral_clearing_finite_bounds T U
  obtain ⟨C0,hC0,hconj,δ0,hδ0,hδbound0,hint0⟩ := ha
  obtain ⟨hCr,hconjr,hδr,hδboundr,hintr⟩ :=
    ordinaryDerivative_common_arithmetic_bounds a C0 hC0 hconj δ0 hδ0 hδbound0 hint0 r
  obtain ⟨_,hint,hhouse⟩ :=
    strictE_derivative_prefix_integral_house F a hmem C0 hC0 hconj δ0 hδ0 hδbound0 hint0 r
  have hlift : strictEFieldCoefficient F a hmem = ordinaryBorelFieldCoefficient F a hmem := rfl
  rw [hlift] at hint hhouse
  let δ := fun L => δ0 (L+r)
  let b : ℕ → Fin r → ℕ → 𝓞 F := fun L i n =>
    if hn : n ≤ L then ⟨(δ L:F)*PowerSeries.coeff F n (f i), hint i L n hn⟩ else 0
  have hb (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      (b L i n : F) = (δ L:F)*PowerSeries.coeff F n (f i) := by simp only [b, dif_pos hn] <;> rfl
  have hbH (L : ℕ) (i : Fin r) (n : ℕ) (hn : n ≤ L) :
      NumberField.house (b L i n : F) ≤
        (ordinaryDerivativeArithmeticConstant C0 r)^(2*(L+1)) := by
    rw [hb L i n hn]
    exact hhouse i L n hn
  obtain ⟨E,hE,hq⟩ := exists_typeII_system_exponential_denominators hr T U A f
    e τ HT (ordinaryDerivativeArithmeticConstant C0 r) hHT hCr hli hT0' hTτ hUτ hTe hTH
    hclear hf δ hδr hδboundr b hb hbH
  exact ⟨hdata,T,UI,hTmap,hclear,E,hE,hq⟩

end StrictEUnit
end
