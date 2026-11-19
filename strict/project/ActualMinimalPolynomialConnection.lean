import PolynomialConnectionClearing
import OrdinaryBorelMinimalCyclic

/-! SOURCE ONLY. Actual Stage14 rational derivative and literal minimal
companion of the original input. Clearing data are universally retained,
not reselected. Polynomial coefficients are not asserted integral. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The actual Stage14 polynomial compatibility discharges the generic premise
for any SAME supplied matrix A and clearing T/U. -/
theorem stage14_polynomial_connection_maps
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * A i j) :
    (∀ n i j, algebraMap (Polynomial K) (RatFunc K)
      (polynomialConnectionSequence T U n i j) =
        (algebraMap (Polynomial K) (RatFunc K) T)^n *
          matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i j) ∧
    (∀ n i j, algebraMap (Polynomial K) (RatFunc K)
      (dividedPolynomialConnectionSequence T U n i j) =
        (n.factorial : RatFunc K)⁻¹ * (algebraMap (Polynomial K) (RatFunc K) T)^n *
          matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i j) := by
  have hcompat : ∀ p : Polynomial K,
      stage14_rationalOrdinaryDerivation (algebraMap (Polynomial K) (RatFunc K) p) =
        algebraMap (Polynomial K) (RatFunc K) p.derivative :=
    stage14_rationalOrdinaryDerivation_polynomial
  exact ⟨polynomialConnectionSequence_map stage14_rationalOrdinaryDerivation
      (algebraMap (Polynomial K) (RatFunc K)) hcompat T U A hclear,
    fun n => dividedPolynomialConnectionSequence_map stage14_rationalOrdinaryDerivation
      (algebraMap (Polynomial K) (RatFunc K)) hcompat T U A hclear n⟩

/-- A transparent package for the SAME minimal companion. It quantifies over
all clearing pairs, so it applies to an existing common integral clearing too. -/
def OrdinaryBorelPolynomialConnectionData
    {K : Type*} [Field K] [CharZero K] (G : LaurentSeries K)
    (r : ℕ) (b : Fin r → RatFunc K) : Prop :=
  OrdinaryBorelMinimalCyclicData G r b ∧
  ∀ (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)),
    (∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T * minimalDerivativeCompanion r b i j) →
    (∀ n i j, algebraMap (Polynomial K) (RatFunc K)
      (polynomialConnectionSequence T U n i j) =
        (algebraMap (Polynomial K) (RatFunc K) T)^n *
          matrixConnectionSequence stage14_rationalOrdinaryDerivation
            (minimalDerivativeCompanion r b) n i j) ∧
    (∀ n i j, algebraMap (Polynomial K) (RatFunc K)
      (dividedPolynomialConnectionSequence T U n i j) =
        (n.factorial : RatFunc K)⁻¹ * (algebraMap (Polynomial K) (RatFunc K) T)^n *
          matrixConnectionSequence stage14_rationalOrdinaryDerivation
            (minimalDerivativeCompanion r b) n i j)

theorem ordinaryBorelMinimalCyclic_polynomial_connection
    {K : Type*} [Field K] [CharZero K] (G : LaurentSeries K)
    (r : ℕ) (b : Fin r → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData G r b) :
    OrdinaryBorelPolynomialConnectionData G r b := by
  refine ⟨hdata, ?_⟩
  intro T U hclear
  exact stage14_polynomial_connection_maps (minimalDerivativeCompanion r b) T U hclear

/-- Choose the existing original-input witnesses only once, and attach the
polynomial H_n formulas to that exact minimal companion. No compatibility,
polynomial-membership, or alternative-system premise is added. -/
theorem stage41_ordinary_borel_same_input_polynomial_connection
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a)
    (hne : ∃ n, a n ≠ 0) :
    ∃ m : ℕ, ∃ q : Fin (m+1) → Polynomial AlgebraicComplex,
      ∃ F : IntermediateField ℚ AlgebraicComplex,
      ∃ hmem : ∀ n, a n ∈ F, ∃ qF : Fin (m+1) → Polynomial F,
        FiniteDimensional ℚ F ∧
        (∀ i, (qF i).map (algebraMap F AlgebraicComplex) = q i) ∧
        (∃ i, q i ≠ 0) ∧ (∃ i, qF i ≠ 0) ∧
        (∑ i, algebraMap (Polynomial F) (LaurentSeries F) (qF i) *
          (laurentOrdinaryDerivation : LaurentSeries F → LaurentSeries F)^[i.val]
            (HahnSeries.ofPowerSeries ℤ F
              (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)))) = 0 ∧
        (∃ r, 0 < r ∧ ∃ b : Fin r → RatFunc F,
          OrdinaryBorelPolynomialConnectionData
            (HahnSeries.ofPowerSeries ℤ F
              (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) r b) ∧
        HasStrictEArithmetic a := by
  obtain ⟨m,q,F,hmem,qF,hfinite,hmap,hq,hqF,hode,hminimal,harith⟩ :=
    stage41_ordinary_borel_same_input_minimal_cyclic a ha hne
  obtain ⟨r,hr,b,hdata⟩ := hminimal
  exact ⟨m,q,F,hmem,qF,hfinite,hmap,hq,hqF,hode,
    ⟨r,hr,b,ordinaryBorelMinimalCyclic_polynomial_connection _ r b hdata⟩,harith⟩

end StrictEUnit
end
