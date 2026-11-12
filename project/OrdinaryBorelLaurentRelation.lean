import OrdinaryBorelFieldDescent
import Stage14LaurentPolynomialODEClosure

/-! NEW SOURCE-ONLY, UNCOMPILED. Literal ordinary-series embedding into the
Laurent field, with its actual ordinary derivative and rational scalars.
The derivative is NOT asserted RatFunc-linear. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- The same polynomial tuple annihilates the exact Laurent embedding. -/
theorem ordinaryBorel_laurent_equation {K : Type*} [Field K]
    (G : PowerSeries K) (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (hode : (∑ i, (q i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] G) = 0) :
    (∑ i, algebraMap (Polynomial K) (LaurentSeries K) (q i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (HahnSeries.ofPowerSeries ℤ K G)) = 0 := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ K) hode
  rw [map_sum, map_zero] at h
  calc
    _ = ∑ i, HahnSeries.ofPowerSeries ℤ K
        ((q i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] G) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Polynomial.algebraMap_hahnSeries_apply,
        laurentOrdinaryDerivation_iterate_ofPowerSeries, map_mul]
    _ = 0 := h

/-- A genuinely nonzero polynomial ODE gives a rational scalar relation for
this same Laurent series, via the existing Stage14 equivalence. -/
theorem ordinaryBorel_laurent_scalar_relation {K : Type*} [Field K]
    (G : PowerSeries K) (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (hq : ∃ i, q i ≠ 0)
    (hode : (∑ i, (q i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] G) = 0) :
    HasScalarLinearDifferentialRelation (B := RatFunc K)
      (stage14_laurentAlgebraDerivation (k := K)) (HahnSeries.ofPowerSeries ℤ K G) := by
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  apply (stage14_polynomialScalarRelation_iff stage14_laurentAlgebraDerivation _).mp
  refine ⟨m, q, hq, ?_⟩
  have h := ordinaryBorel_laurent_equation G m q hode
  calc
    _ = ∑ i, algebraMap (Polynomial K) (LaurentSeries K) (q i) *
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (HahnSeries.ofPowerSeries ℤ K G) := by
      apply Finset.sum_congr rfl
      intro i hi
      change algebraMap (RatFunc K) (LaurentSeries K)
          (algebraMap (Polynomial K) (RatFunc K) (q i)) *
          (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
            (HahnSeries.ofPowerSeries ℤ K G) = _
      rw [← IsScalarTower.algebraMap_apply
        (Polynomial K) (RatFunc K) (LaurentSeries K)]
    _ = 0 := h

/-- Nonzero Laurent input is asserted only from an actual nonzero coefficient. -/
theorem ordinaryBorel_laurent_mk_ne_zero {K : Type*} [Field K]
    (a : ℕ → K) (ha : ∃ n, a n ≠ 0) :
    HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk a) ≠ 0 := by
  intro h
  have hG : PowerSeries.mk a = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
    (by simpa only [map_zero] using h)
  obtain ⟨n, hn⟩ := ha
  have hc := congrArg (PowerSeries.coeff K n) hG
  rw [PowerSeries.coeff_mk, map_zero] at hc
  exact hn hc

/-- Generic presentation of the exact scalar-relation predicate. The canonical
instances are elaborated over abstract K, avoiding repeated concrete subtype
instance search. This is a definition, not an additional hypothesis. -/
def OrdinaryBorelLaurentScalarRelation {K : Type*} [Field K]
    (G : PowerSeries K) : Prop :=
  HasScalarLinearDifferentialRelation (B := RatFunc K)
    (stage14_laurentAlgebraDerivation (k := K)) (HahnSeries.ofPowerSeries ℤ K G)

/-- Same original finite-field witnesses, same lifted tuple, exact Laurent
polynomial equation and rational relation. Nonzero input remains conditional. -/
theorem stage41_ordinary_borel_finite_field_laurent_relation
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    ∃ m : ℕ, ∃ q : Fin (m+1) → Polynomial AlgebraicComplex,
      ∃ F : IntermediateField ℚ AlgebraicComplex,
      ∃ hmem : ∀ n, a n ∈ F, ∃ qF : Fin (m+1) → Polynomial F,
        FiniteDimensional ℚ F ∧
        (∀ i, (qF i).map (algebraMap F AlgebraicComplex) = q i) ∧
        (∃ i, q i ≠ 0) ∧ (∃ i, qF i ≠ 0) ∧
        (∑ i, (qF i : PowerSeries F) *
          (PowerSeries.derivative F)^[i.val]
            (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) = 0 ∧
        (∑ i, algebraMap (Polynomial F) (LaurentSeries F) (qF i) *
          (laurentOrdinaryDerivation : LaurentSeries F → LaurentSeries F)^[i.val]
            (HahnSeries.ofPowerSeries ℤ F
              (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)))) = 0 ∧
        OrdinaryBorelLaurentScalarRelation
          (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) ∧
        ((∃ n, a n ≠ 0) → HahnSeries.ofPowerSeries ℤ F
          (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) ≠ 0) ∧
        HasStrictEArithmetic a := by
  obtain ⟨m, q, F, hmem, qF, hfinite, hmap, hq, hqF, hode, hodeF, harith⟩ :=
    stage41_ordinary_borel_finite_field_ode a ha
  refine ⟨m, q, F, hmem, qF, hfinite, hmap, hq, hqF, hodeF,
    ordinaryBorel_laurent_equation _ m qF hodeF,
    ordinaryBorel_laurent_scalar_relation _ m qF hqF hodeF, ?_, harith⟩
  intro hnonzero
  apply ordinaryBorel_laurent_mk_ne_zero
  obtain ⟨n, hn⟩ := hnonzero
  refine ⟨n, ?_⟩
  intro hz
  apply hn
  exact congrArg (fun x : F => (x : AlgebraicComplex)) hz

end StrictEUnit
end
