import OrdinaryBorelFieldDescent
import ReciprocalValuationDegree

/-! An injective coefficient-field map preserves the literal tuple, its
trailing degrees, local regularity inequalities, and exact scalar equation. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

theorem polynomial_natTrailingDegree_map (φ : K →+* L) (p : Polynomial K) :
    (p.map φ).natTrailingDegree = p.natTrailingDegree := by
  unfold Polynomial.natTrailingDegree Polynomial.trailingDegree
  rw [Polynomial.support_map_of_injective p φ.injective]

theorem reciprocalRegularSingularBounds_map (φ : K →+* L)
    (r : ℕ) (q : Fin (r+1) → Polynomial K)
    (hreg : ReciprocalRegularSingularBounds r q) :
    ReciprocalRegularSingularBounds r (fun i => (q i).map φ) := by
  intro i hi
  have hqi : q i ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).1 hi
  simpa only [polynomial_natTrailingDegree_map] using hreg i hqi

theorem ordinaryTuple_equation_map (φ : K →+* L)
    (r : ℕ) (q : Fin (r+1) → Polynomial K) (G : PowerSeries K)
    (hode : (∑ i, (q i : PowerSeries K) * (PowerSeries.derivative K)^[i.val] G) = 0) :
    (∑ i, ((q i).map φ : PowerSeries L) *
      (PowerSeries.derivative L)^[i.val] (PowerSeries.map φ G)) = 0 := by
  have hm := congrArg (PowerSeries.map φ) hode
  rw [map_sum, map_zero] at hm
  calc
    _ = ∑ i, PowerSeries.map φ ((q i : PowerSeries K) *
        (PowerSeries.derivative K)^[i.val] G) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_mul, ordinaryBorel_map_iterate_derivative,
        ← Polynomial.polynomial_map_coe]
    _ = 0 := hm

theorem ordinaryFieldTuple_map
    (F : IntermediateField ℚ AlgebraicComplex) (a : ℕ → AlgebraicComplex)
    (hmem : ∀ n, a n ∈ F) (r : ℕ) (q : Fin (r+1) → Polynomial F)
    (htop : q (Fin.last r) ≠ 0)
    (hreg : ReciprocalRegularSingularBounds r q)
    (hode : (∑ i, (q i : PowerSeries F) * (PowerSeries.derivative F)^[i.val]
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) = 0) :
    let p : Fin (r+1) → Polynomial AlgebraicComplex :=
      fun i => (q i).map (algebraMap F AlgebraicComplex)
    p (Fin.last r) ≠ 0 ∧ ReciprocalRegularSingularBounds r p ∧
      (∑ i, (p i : PowerSeries AlgebraicComplex) *
        (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 := by
  let φ : F →+* AlgebraicComplex := algebraMap F AlgebraicComplex
  have hseries : PowerSeries.map φ
      (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) = PowerSeries.mk a := by
    ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
    rfl
  refine ⟨(Polynomial.map_ne_zero_iff φ.injective).2 htop,
    reciprocalRegularSingularBounds_map φ r q hreg, ?_⟩
  have h := ordinaryTuple_equation_map φ r q
    (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) hode
  simpa only [hseries] using h

end StrictEUnit
end
