import V5BroadEntireRegularity
import Stage26StrictEFiniteCoefficientField
import Mathlib.Algebra.Algebra.Hom.Rat

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Broad arithmetic expressed before a coefficient number field is chosen. -/
def V5BroadAlgebraicArithmetic (a : ℕ → AlgebraicComplex) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 1 ≤ C ∧ ∃ δ : ℕ → ℕ, (∀ L, 0 < δ L) ∧
      (∀ L, (δ L : ℝ) ≤ C^(L+1) * (L.factorial : ℝ)^ε) ∧
      (∀ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n,
        ‖τ (a n)‖ ≤ C^(n+1) * (n.factorial : ℝ)^ε) ∧
      (∀ L n, n ≤ L → IsIntegral ℤ ((δ L : ℂ) * (a n : ℂ)))

theorem v5_broad_arithmetic_descends (F : IntermediateField ℚ AlgebraicComplex)
    [NumberField F] (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F)
    (ha : V5BroadAlgebraicArithmetic a) :
    V5BroadArithmetic (ordinaryBorelFieldCoefficient F a hmem) := by
  let b := ordinaryBorelFieldCoefficient F a hmem
  intro ε hε
  obtain ⟨C,hC,δ,hδ,hδb,hh,hi⟩ := ha ε hε
  refine ⟨C,hC,δ,hδ,hδb,?_,?_⟩
  · intro n
    change ‖NumberField.canonicalEmbedding F (b n)‖ ≤ _
    apply (NumberField.canonicalEmbedding.norm_le_iff _ _).mpr
    intro σ
    obtain ⟨τ, hτ⟩ := algebraicComplex_embedding_extends F σ.toRatAlgHom
    change ‖σ.toRatAlgHom (b n)‖ ≤ _
    rw [← hτ (b n)]
    exact hh τ n
  · intro L n hn
    let e : F →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val.comp F.val
    apply (isIntegral_algHom_iff (e.restrictScalars ℤ) e.injective).mp
    change IsIntegral ℤ (((δ L : F) * b n : F) : AlgebraicComplex).val
    simpa only [IntermediateField.coe_mul, map_natCast] using hi L n hn

/-- The factorial normalization and its differential equation descend together
to a single field obtained by finite generation from the equation. -/
theorem v5_broad_factorial_ode_descends (a : ℕ → AlgebraicComplex)
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex)
    (hp : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))) = 0) :
    ∃ F : IntermediateField ℚ AlgebraicComplex, ∃ hmem : ∀ n, a n ∈ F,
      ∃ q : Fin (m+1) → Polynomial F, FiniteDimensional ℚ F ∧
        (∀ i, (q i).map (algebraMap F AlgebraicComplex) = p i) ∧
        (∃ i, q i ≠ 0) ∧
        ∑ i, (q i : PowerSeries F) * (PowerSeries.derivative F)^[i.val]
          (PowerSeries.mk (fun n =>
            ordinaryBorelFieldCoefficient F a hmem n / (n.factorial : F))) = 0 := by
  let x : ℕ → AlgebraicComplex := fun n => a n / (n.factorial : AlgebraicComplex)
  obtain ⟨F,hF,hx,hpF⟩ :=
    stage26_formal_ode_finite_coefficient_field m p (PowerSeries.mk x) hp hode
  have hx' (n : ℕ) : x n ∈ F := by simpa only [PowerSeries.coeff_mk] using hx n
  have haF (n : ℕ) : a n ∈ F := by
    have hn : (n.factorial : AlgebraicComplex) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    have h := F.mul_mem (hx' n) (F.natCast_mem n.factorial)
    simpa only [x, div_mul_cancel₀ _ hn] using h
  obtain ⟨q,hmap,hneq,hq⟩ := ordinaryBorel_equation_descends F x hx' m p hpF hp hode
  have heq (n : ℕ) : ordinaryBorelFieldCoefficient F x hx' n =
      ordinaryBorelFieldCoefficient F a haF n / (n.factorial : F) := by
    apply Subtype.ext
    change x n = algebraMap F AlgebraicComplex
      (ordinaryBorelFieldCoefficient F a haF n / (n.factorial : F))
    rw [map_div₀, map_natCast]
    rfl
  rw [funext heq] at hq
  exact ⟨F,haF,q,hF,hmap,hneq,hq⟩

/-- Exact Taylor data and a formal equation over the algebraic numbers, with
usual broad growth and denominators, give the actual entire regular operator. -/
theorem v5_broad_algebraic_entire_annihilator
    (f : entireFunctionAlgebra) (hf : f ≠ 0)
    (a : ℕ → AlgebraicComplex) (ha : V5BroadAlgebraicArithmetic a)
    (hc : ∀ n, (a n : ℂ) = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex)
    (hp : ∃ i, p i ≠ 0)
    (hode : ∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))) = 0) :
    ∃ (n : ℕ) (P : ℕ → Polynomial ℂ), 0 < n ∧
      (∀ z, v5RowResidual f.val n P z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (P n).eval z ≠ 0 := by
  classical
  obtain ⟨F,hmem,q,hF,_,hq,hqode⟩ := v5_broad_factorial_ode_descends a m p hp hode
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := ⟨⟩
  let b := ordinaryBorelFieldCoefficient F a hmem
  let e : F →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val.comp F.val
  have hne : ∃ n, b n ≠ 0 := by
    by_contra! hz
    apply hf
    apply entireTaylorAlgHom_injective
    rw [map_zero]
    ext n
    have hc' : e (b n) = v5FactorialCoeff (entireTaylorAlgHom f) n := hc n
    rw [hz n, map_zero, v5FactorialCoeff] at hc'
    rw [map_zero]
    exact (mul_eq_zero.mp hc'.symm).resolve_left
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
  exact v5_broad_entire_annihilator_ordinary_off_zero e.toRingHom b
    (v5_broad_arithmetic_descends F a hmem ha) hne f hc m q hq hqode

#print axioms v5_broad_arithmetic_descends
#print axioms v5_broad_factorial_ode_descends
#print axioms v5_broad_algebraic_entire_annihilator
end StrictEUnit
end
