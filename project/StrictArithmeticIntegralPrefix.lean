import Stage44StrictECoefficientHeight
import Mathlib.NumberTheory.NumberField.House
import Mathlib.Algebra.Algebra.Hom.Rat

/-! NEW SOURCE-ONLY, UNCOMPILED. Integral initial segments of the SAME strict
arithmetic coefficients inside the SAME supplied finite intermediate field.
The original arithmetic constant and denominator sequence are extracted once
and retained, not replaced by a height certificate or a new series.

Existing chosen-embedding integrality descent and algebraic embedding extension
are reused. The new endpoint is a literal ring-of-integers prefix and a uniform
house bound, suitable as input to a separate finite-matrix approximation theorem.
No Padé vector, global continuation, G-operator, Fuchs property, or arithmetic
local-solution family is constructed here. No option/instance priority is changed.
-/
noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- The supplied coefficient itself, viewed in the supplied containing field. -/
def strictEFieldCoefficient (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F) (n : ℕ) : F :=
  ⟨a n, hmem n⟩

theorem strictEFieldCoefficient_coe (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F) (n : ℕ) :
    (strictEFieldCoefficient F a hmem n : AlgebraicComplex) = a n := rfl

/-- Every ring embedding of F is bounded by the SAME supplied conjugate bound,
by extending its rational-algebra-hom interpretation to all algebraic numbers. -/
theorem strictEFieldCoefficient_embedding_bound
    (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F)
    (C : ℝ)
    (hconj : ∀ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖τ (a n)‖ ≤ C^(n + 1))
    (σ : F →+* ℂ) (n : ℕ) :
    ‖σ (strictEFieldCoefficient F a hmem n)‖ ≤ C^(n + 1) := by
  obtain ⟨τ, hτ⟩ := algebraicComplex_embedding_extends F σ.toRatAlgHom
  change ‖σ.toRatAlgHom (strictEFieldCoefficient F a hmem n)‖ ≤ C^(n + 1)
  rw [← hτ (strictEFieldCoefficient F a hmem n)]
  exact hconj τ n

/-- Clear each finite prefix using the supplied original common denominator.
Integrality is reflected from the given chosen complex embedding; no integral
membership is assumed directly in F. The prefix includes index zero. -/
def strictEIntegralPrefix (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F) (d : ℕ → ℕ)
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((d N : ℂ) * (a j : ℂ)))
    (N : ℕ) (j : Fin (N + 1)) : 𝓞 F :=
  ⟨(d N : F) * strictEFieldCoefficient F a hmem j.val,
    stage44_integral_coefficient_denominator F
      (strictEFieldCoefficient F a hmem)
      (strictEFieldCoefficient_coe F a hmem) (d N) j.val
      (hint N j.val (Nat.le_of_lt_succ j.isLt))⟩

/-- The ring-of-integers prefix has exactly the intended underlying coefficient. -/
theorem strictEIntegralPrefix_coe (F : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F) (d : ℕ → ℕ)
    (hint : ∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((d N : ℂ) * (a j : ℂ)))
    (N : ℕ) (j : Fin (N + 1)) :
    (strictEIntegralPrefix F a hmem d hint N j : F) =
      (d N : F) * strictEFieldCoefficient F a hmem j.val := rfl

/-- Denominator and conjugate bounds with the SAME C give a uniform house
bound for every entry of the cleared prefix, including N=0 and j=0. -/
theorem strictEFieldCoefficient_scaled_house_le
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    (a : ℕ → AlgebraicComplex) (hmem : ∀ n, a n ∈ F)
    (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖τ (a n)‖ ≤ C^(n + 1))
    (d N j : ℕ) (hd : (d : ℝ) ≤ C^(N + 1)) (hj : j ≤ N) :
    NumberField.house ((d : F) * strictEFieldCoefficient F a hmem j) ≤
      C^(2 * (N + 1)) := by
  change ‖NumberField.canonicalEmbedding F
    ((d : F) * strictEFieldCoefficient F a hmem j)‖ ≤ C^(2 * (N + 1))
  apply (NumberField.canonicalEmbedding.norm_le_iff _ _).mpr
  intro σ
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  have hbound : ‖σ (strictEFieldCoefficient F a hmem j)‖ ≤ C^(N + 1) :=
    (strictEFieldCoefficient_embedding_bound F a hmem C hconj σ j).trans
      (pow_le_pow_right₀ hC (Nat.add_le_add_right hj 1))
  calc
    (d : ℝ) * ‖σ (strictEFieldCoefficient F a hmem j)‖ ≤
        C^(N + 1) * C^(N + 1) :=
      mul_le_mul hd hbound (norm_nonneg _) (pow_nonneg (zero_le_one.trans hC) _)
    _ = C^(2 * (N + 1)) := by
      rw [← pow_add]
      congr 1
      omega

/-- From actual strict arithmetic and the supplied finite containing field,
construct literal integral prefixes with a uniform house bound. The conclusion
retains ALL original conditions on the same C and d, and displays both the
F-valued and ambient coefficient equalities. NumberField F is derived from the
given finite-dimensionality, not supplied as an independent hypothesis. -/
theorem strictEArithmetic_exists_integral_prefix
    (F : IntermediateField ℚ AlgebraicComplex) (hfinite : FiniteDimensional ℚ F)
    (a : ℕ → AlgebraicComplex) (ha : HasStrictEArithmetic a)
    (hmem : ∀ n, a n ∈ F) :
    ∃ hNF : NumberField F, ∃ C : ℝ, 1 ≤ C ∧ ∃ d : ℕ → ℕ,
      (∀ N, 0 < d N) ∧
      (∀ N, (d N : ℝ) ≤ C^(N + 1)) ∧
      (∀ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ n, ‖τ (a n)‖ ≤ C^(n + 1)) ∧
      (∀ N j : ℕ, j ≤ N → IsIntegral ℤ ((d N : ℂ) * (a j : ℂ))) ∧
      ∃ b : (N : ℕ) → Fin (N + 1) → 𝓞 F,
        (∀ N j, (b N j : F) = (d N : F) * strictEFieldCoefficient F a hmem j.val) ∧
        (∀ N j, @NumberField.house F _ hNF (b N j : F) ≤ C^(2 * (N + 1))) ∧
        (∀ N j, ((b N j : F) : AlgebraicComplex) =
          (d N : AlgebraicComplex) * a j.val) := by
  letI : FiniteDimensional ℚ F := hfinite
  letI : NumberField F := ⟨⟩
  obtain ⟨C, hC, hconj, d, hd, hdbound, hint⟩ := ha
  refine ⟨inferInstance, C, hC, d, hd, hdbound, hconj, hint,
    strictEIntegralPrefix F a hmem d hint, ?_, ?_, ?_⟩
  · intro N j
    rfl
  · intro N j
    rw [strictEIntegralPrefix_coe]
    exact strictEFieldCoefficient_scaled_house_le F a hmem C hC hconj
      (d N) N j.val (hdbound N) (Nat.le_of_lt_succ j.isLt)
  · intro N j
    rw [strictEIntegralPrefix_coe]
    change F.val ((d N : F) * strictEFieldCoefficient F a hmem j.val) = _
    rw [map_mul, map_natCast] <;> rfl

end StrictEUnit
end
