import OrdinaryBorelJointData
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.PowerSeries.Derivative

/-! NEW SOURCE-ONLY, UNCOMPILED. Exact coefficient-field descent for the same
ordinary Borel series and the same polynomial tuple. No House import,
minimality, regularity, G-operator, or arithmetic local-family assumption. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- Literal subtype coefficients, without any choice of new values. -/
def ordinaryBorelFieldCoefficient (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F) (n : ℕ) : F :=
  ⟨a n, hmem n⟩

theorem ordinaryBorel_map_derivative {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : PowerSeries R) :
    PowerSeries.map φ (PowerSeries.derivative R f) =
      PowerSeries.derivative S (PowerSeries.map φ f) := by
  ext n
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_derivative,
    map_mul, map_add, map_natCast, map_one]

theorem ordinaryBorel_map_iterate_derivative {R S : Type*}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (n : ℕ) (f : PowerSeries R) :
    PowerSeries.map φ ((PowerSeries.derivative R)^[n] f) =
      (PowerSeries.derivative S)^[n] (PowerSeries.map φ f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ordinaryBorel_map_derivative,
      ih, Function.iterate_succ_apply']

/-- Every coefficient is in the original field, hence the polynomial itself
is the image of a polynomial over that field. -/
theorem ordinaryBorel_polynomial_lift (F : IntermediateField ℚ AlgebraicComplex)
    (q : Polynomial AlgebraicComplex) (hmem : ∀ n, q.coeff n ∈ F) :
    ∃ qF : Polynomial F, qF.map (algebraMap F AlgebraicComplex) = q := by
  apply (Polynomial.mem_lifts q).mp
  apply (Polynomial.lifts_iff_coeff_lifts q).mpr
  intro n
  exact ⟨⟨q.coeff n, hmem n⟩, rfl⟩

/-- Descend the exact supplied tuple and exact ordinary-series equation.
Only coefficient membership is used; the tuple is not replaced by another ODE. -/
theorem ordinaryBorel_equation_descends
    (F : IntermediateField ℚ AlgebraicComplex) (a : ℕ → AlgebraicComplex)
    (hmem : ∀ n, a n ∈ F) (m : ℕ) (q : Fin (m+1) → Polynomial AlgebraicComplex)
    (hqmem : ∀ i n, (q i).coeff n ∈ F) (hq : ∃ i, q i ≠ 0)
    (hode : (∑ i, (q i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0) :
    ∃ qF : Fin (m+1) → Polynomial F,
      (∀ i, (qF i).map (algebraMap F AlgebraicComplex) = q i) ∧
      (∃ i, qF i ≠ 0) ∧
      (∑ i, (qF i : PowerSeries F) *
        (PowerSeries.derivative F)^[i.val]
          (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) = 0 := by
  choose qF hmap using fun i => ordinaryBorel_polynomial_lift F (q i) (hqmem i)
  refine ⟨qF, hmap, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hq
    refine ⟨i, ?_⟩
    intro hz
    apply hi
    rw [← hmap i, hz, Polynomial.map_zero]
  · let φ : F →+* AlgebraicComplex := algebraMap F AlgebraicComplex
    have hseries : PowerSeries.map φ
        (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem)) = PowerSeries.mk a := by
      ext n
      rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
      rfl
    apply PowerSeries.map_injective φ φ.injective
    rw [map_zero, map_sum]
    calc
      _ = ∑ i, (q i : PowerSeries AlgebraicComplex) *
          (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_mul, ordinaryBorel_map_iterate_derivative, hseries,
          ← Polynomial.polynomial_map_coe]
        rw [show (qF i).map φ = q i from hmap i]
      _ = 0 := hode

/-- Actual joint data supplies the common finite field and coefficient
membership. Retains original a, original q, the exact lifted qF and arithmetic. -/
theorem stage41_ordinary_borel_finite_field_ode
    (a : ℕ → AlgebraicComplex) (ha : Stage41IsStrictESeries a) :
    ∃ m : ℕ, ∃ q : Fin (m+1) → Polynomial AlgebraicComplex,
      ∃ F : IntermediateField ℚ AlgebraicComplex,
      ∃ hmem : ∀ n, a n ∈ F, ∃ qF : Fin (m+1) → Polynomial F,
        FiniteDimensional ℚ F ∧
        (∀ i, (qF i).map (algebraMap F AlgebraicComplex) = q i) ∧
        (∃ i, q i ≠ 0) ∧ (∃ i, qF i ≠ 0) ∧
        (∑ i, (q i : PowerSeries AlgebraicComplex) *
          (PowerSeries.derivative AlgebraicComplex)^[i.val] (PowerSeries.mk a)) = 0 ∧
        (∑ i, (qF i : PowerSeries F) *
          (PowerSeries.derivative F)^[i.val]
            (PowerSeries.mk (ordinaryBorelFieldCoefficient F a hmem))) = 0 ∧
        HasStrictEArithmetic a := by
  obtain ⟨m, q, F, hq, hode, hfinite, hmem, hqmem, harith⟩ :=
    stage41_ordinary_borel_joint_data a ha
  obtain ⟨qF, hmap, hqF, hodeF⟩ :=
    ordinaryBorel_equation_descends F a hmem m q hqmem hq hode
  exact ⟨m, q, F, hmem, qF, hfinite, hmap, hq, hqF, hode, hodeF, harith⟩

end StrictEUnit
end
