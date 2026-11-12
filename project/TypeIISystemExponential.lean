import TypeIIJointArithmeticAssembly
import UniformPolynomialDualAnnihilatorExistence

/-! Discharge the uniform-D premise; SAME system/arithmetic data retained. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

theorem exists_typeII_system_exponential_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (e τ : ℕ) (HT C : ℝ) (hHT : 1 ≤ HT) (hC : 1 ≤ C)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ) (hTe : T.natDegree ≤ e)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (δ : ℕ → ℕ) (hδ : ∀ L, 0 < δ L)
    (hδbound : ∀ L, (δ L : ℝ) ≤ C^(L+1))
    (b : ℕ → Fin r → ℕ → 𝓞 K)
    (hb : ∀ L i n, n ≤ L → (b L i n : K) = (δ L : K)*PowerSeries.coeff K n (f i))
    (hhouse : ∀ L i n, n ≤ L → NumberField.house (b L i n : K) ≤ C^(2*(L+1))) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ E^(s+1) ∧
      ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((q:K)*
          (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  obtain ⟨D,hD⟩ := exists_uniform_polynomial_dual_annihilator A
  exact exists_typeII_arithmetic_exponential_denominators hr T U A f e τ D HT C
    hHT hC hD hli hT0 hT hU hTe hTH hclear hf δ hδ hδbound b hb hhouse

end StrictEUnit
end
