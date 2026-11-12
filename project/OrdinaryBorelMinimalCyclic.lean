import OrdinaryBorelLaurentRelation
import MinimalDifferentialCompanion

/-! SOURCE ONLY. Dependencies Laurent relation and generic companion require
separate successful validation; this file adds no hypotheses replacing their proofs.
No regularity, Galochkin estimate or arithmetic solution family is asserted. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Minimal cyclic data for the actual Laurent ordinary derivative, with rational
scalars. The displayed span, recurrence and companion all use the same G. -/
def OrdinaryBorelMinimalCyclicData {K : Type*} [Field K]
    (G : LaurentSeries K) (r : ℕ) (b : Fin r → RatFunc K) : Prop :=
  let D : LaurentSeries K → LaurentSeries K := laurentOrdinaryDerivation
  LinearIndependent (RatFunc K) (fun i : Fin r => D^[i.val] G) ∧
  (∑ i, b i • D^[i.val] G = D^[r] G) ∧
  (∀ b' : Fin r → RatFunc K, (∑ i, b' i • D^[i.val] G = D^[r] G) → b' = b) ∧
  (∀ x ∈ Submodule.span (RatFunc K) (Set.range (fun i : Fin r => D^[i.val] G)),
    D x ∈ Submodule.span (RatFunc K) (Set.range (fun i : Fin r => D^[i.val] G))) ∧
  (∀ i : Fin r, D (D^[i.val] G) = ∑ j, minimalDerivativeCompanion r b i j • D^[j.val] G)

/-- Rational scalar compatibility is derived from the exact Stage14 inclusion,
not supplied as an extra endpoint assumption and not replaced by RatFunc-linearity. -/
theorem ordinaryBorel_exists_minimal_cyclic {K : Type*} [Field K]
    (G : LaurentSeries K) (hG : G ≠ 0)
    (hrel : HasScalarLinearDifferentialRelation (B := RatFunc K)
      (stage14_laurentAlgebraDerivation (k := K)) G) :
    ∃ r, 0 < r ∧ ∃ b : Fin r → RatFunc K, OrdinaryBorelMinimalCyclicData G r b := by
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  obtain ⟨m, c, hc, heq⟩ := hrel
  have hcompat : ∀ b : RatFunc K,
      stage14_laurentAlgebraDerivation (algebraMap (RatFunc K) (LaurentSeries K) b) =
      algebraMap (RatFunc K) (LaurentSeries K) (stage14_rationalOrdinaryDerivation b) :=
    stage14_rationalLaurent_differential
  obtain ⟨r, hpos, _hr, b, hli, hrec, huniq, hstable, hrows⟩ :=
    exists_minimal_derivative_companion stage14_rationalOrdinaryDerivation
      stage14_laurentAlgebraDerivation hcompat G hG m c hc heq
  exact ⟨r, hpos, b, hli, hrec, huniq, hstable, hrows⟩

/-- The nonzero original coefficient supplies nonzero G; choose the field and
polynomial tuple only once and retain them throughout the minimal construction. -/
theorem stage41_ordinary_borel_same_input_minimal_cyclic
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
          OrdinaryBorelMinimalCyclicData
            (HahnSeries.ofPowerSeries ℤ F
              (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) r b) ∧
        HasStrictEArithmetic a := by
  obtain ⟨m, q, F, hmem, qF, hfinite, hmap, hq, hqF, _hode,
    hlaurent, hrel, hnonzero, harith⟩ :=
    stage41_ordinary_borel_finite_field_laurent_relation a ha
  exact ⟨m, q, F, hmem, qF, hfinite, hmap, hq, hqF, hlaurent,
    ordinaryBorel_exists_minimal_cyclic _ (hnonzero hne) hrel, harith⟩

/-- Zero original coefficients give the zero literal Laurent input, not a positive
minimal order. This case is kept separate from the preceding theorem. -/
theorem ordinaryBorel_zero_input_laurent
    (a : ℕ → AlgebraicComplex) (ha : ∀ n, a n = 0)
    (F : IntermediateField ℚ AlgebraicComplex) (hmem : ∀ n, a n ∈ F) :
    HahnSeries.ofPowerSeries ℤ F
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) = 0 := by
  have hz : PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem) = 0 := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_mk, map_zero]
    apply Subtype.ext
    exact ha n
  rw [hz, map_zero]

end StrictEUnit
end
