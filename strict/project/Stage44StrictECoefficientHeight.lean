import Stage44NumberFieldHeight
import Stage26StrictEFiniteCoefficientField

/-!
# Strict-E coefficient prefixes have linear fixed-field height

The height estimate is derived from the original all-conjugate/common-denominator
predicate. It is not a new arithmetic assumption. All-index statements use n+1;
the eventual bound uses n. No absolute-height field-independence theorem or deep
arithmetic lifting theorem is proved in this module.
-/

noncomputable section
open scoped BigOperators NumberField
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring

/-- The actual coefficient prefix, including a leading one. -/
def stage44_affinePrefix {K : Type*} [One K] (b : ℕ → K) (n : ℕ) :
    Option (Fin (n + 1)) → K := fun o => o.elim 1 (fun j => b j.val)

/-- Every embedding of a fixed algebraic coefficient field into the complex
numbers extends to an embedding of all algebraic numbers. -/
theorem stage44_extend_coefficient_embedding
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F] (σ : F →ₐ[ℚ] ℂ) :
    ∃ τ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ x : F, τ (x : AlgebraicComplex) = σ x := by
  letI : IsScalarTower ℚ F AlgebraicComplex :=
    IsScalarTower.of_algebraMap_eq (fun q => by simp)
  obtain ⟨τ, hτ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic
    (K := ℚ) (L := F) (E := AlgebraicComplex) (M := ℂ) σ
  exact ⟨τ, fun x => congrArg (fun f : F →ₐ[ℚ] ℂ => f x) hτ⟩

/-- The strict arithmetic predicate's chosen-embedding integrality reflects
back to any coefficient number field. -/
theorem stage44_integral_coefficient_denominator
    (F : IntermediateField ℚ AlgebraicComplex) {a : ℕ → AlgebraicComplex}
    (b : ℕ → F) (hb : ∀ n, (b n : AlgebraicComplex) = a n)
    (d j : ℕ) (hi : IsIntegral ℤ ((d : ℂ) * (a j : ℂ))) :
    IsIntegral ℤ ((d : F) * b j) := by
  let e : F →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val.comp F.val
  apply (isIntegral_algHom_iff (e.restrictScalars ℤ) e.injective).mp
  change IsIntegral ℤ (((d : F) * b j : F) : AlgebraicComplex).val
  simpa only [IntermediateField.coe_mul, map_natCast, hb j] using hi

/-- The sharp prefix bound with the original common arithmetic constant C.
No estimate is assumed about a height, and no normalization C^n is imposed at n=0. -/
theorem stage44_prefix_height_le_of_strict_bounds
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    {a : ℕ → AlgebraicComplex} (b : ℕ → F)
    (hb : ∀ n, (b n : AlgebraicComplex) = a n)
    (C : ℝ) (hC : 1 ≤ C)
    (hconj : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ, ∀ j : ℕ, ‖σ (a j)‖ ≤ C ^ (j + 1))
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (hdbound : ∀ n, (d n : ℝ) ≤ C ^ (n + 1))
    (hint : ∀ n j : ℕ, j ≤ n → IsIntegral ℤ ((d n : ℂ) * (a j : ℂ)))
    (n : ℕ) :
    FixedFieldHeight.height (stage44_affinePrefix b n) ≤
      2 * ((n : ℝ) + 1) * Real.log C := by
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hdenom (j : Fin (n + 1)) : IsIntegral ℤ ((d n : F) * b j.val) :=
    stage44_integral_coefficient_denominator F b hb (d n) j.val
      (hint n j.val (Nat.le_of_lt_succ j.isLt))
  have hbound (σ : F →ₐ[ℚ] ℂ) (j : Fin (n + 1)) :
      ‖σ (b j.val)‖ ≤ C ^ (n + 1) := by
    obtain ⟨τ, hτ⟩ := stage44_extend_coefficient_embedding F σ
    have h := hconj τ j.val
    rw [← hb j.val, hτ (b j.val)] at h
    exact h.trans (pow_le_pow_right₀ hC (by omega))
  have h := FixedFieldHeight.affine_height_le (fun j : Fin (n + 1) => b j.val)
    (d n) (hd n) (C ^ (n + 1)) (one_le_pow₀ hC) hdenom hbound
  have hlogd : Real.log (d n : ℝ) ≤ ((n : ℝ) + 1) * Real.log C := by
    have h := Real.log_le_log (Nat.cast_pos.mpr (hd n)) (hdbound n)
    simpa only [Real.log_pow, Nat.cast_add, Nat.cast_one] using h
  change FixedFieldHeight.height (stage44_affinePrefix b n) ≤ _ at h
  rw [Real.log_pow, Nat.cast_add, Nat.cast_one] at h
  linarith

/-- Genuine height growth follows from HasStrictEArithmetic in every supplied
fixed number field containing its coefficients. -/
theorem stage44_strictArithmetic_fixedField_prefix_height
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    {a : ℕ → AlgebraicComplex} (ha : HasStrictEArithmetic a)
    (b : ℕ → F) (hb : ∀ n, (b n : AlgebraicComplex) = a n) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n,
      FixedFieldHeight.height (stage44_affinePrefix b n) ≤
        2 * ((n : ℝ) + 1) * Real.log C := by
  obtain ⟨C, hC, hconj, d, hd, hdbound, hint⟩ := ha
  exact ⟨C, hC, stage44_prefix_height_le_of_strict_bounds
    F b hb C hC hconj d hd hdbound hint⟩

/-- A concrete eventual linear estimate, including nonnegativity and the
threshold n=1, rather than an invalid all-n bound by A*n. -/
theorem stage44_strictArithmetic_fixedField_eventual_height
    (F : IntermediateField ℚ AlgebraicComplex) [NumberField F]
    {a : ℕ → AlgebraicComplex} (ha : HasStrictEArithmetic a)
    (b : ℕ → F) (hb : ∀ n, (b n : AlgebraicComplex) = a n) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 1 ≤ n →
      0 ≤ FixedFieldHeight.height (stage44_affinePrefix b n) ∧
      FixedFieldHeight.height (stage44_affinePrefix b n) ≤ A * (n : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := stage44_strictArithmetic_fixedField_prefix_height F ha b hb
  have hlog : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨4 * Real.log C, mul_nonneg (by norm_num) hlog, ?_⟩
  intro n hn
  constructor
  · exact FixedFieldHeight.height_nonneg_of_coordinate_one
      ⟨none, by simp [stage44_affinePrefix]⟩
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hlin : 2 * ((n : ℝ) + 1) ≤ 4 * (n : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hlin hlog
    nlinarith [hbound n]

/-- Every strict E-function has a single coefficient number field and its
actual factorial-series coefficients satisfy the proved fixed-field height bound. -/
theorem stage44_strictE_fixed_field_series_height {f : ℂ → ℂ}
    (hf : IsStrictEFunction f) :
    ∃ (F : IntermediateField ℚ AlgebraicComplex) (hF : NumberField F),
      ∃ b : ℕ → F,
        (∀ z : ℂ, HasSum (fun n => ((b n : AlgebraicComplex) : ℂ) * z ^ n /
          (n.factorial : ℂ)) (f z)) ∧
        ∃ A : ℝ, 0 ≤ A ∧ ∀ n,
          @FixedFieldHeight.height F (Option (Fin (n + 1))) _ hF _ _
            (stage44_affinePrefix b n) ≤ A * ((n : ℝ) + 1) := by
  obtain ⟨F, hF, a, hmem, hs, ha⟩ := stage26_strictE_fixed_field_series hf
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := ⟨⟩
  let b : ℕ → F := fun n => ⟨a n, hmem n⟩
  obtain ⟨C, hC, hbound⟩ := stage44_strictArithmetic_fixedField_prefix_height F ha b (fun _ => rfl)
  refine ⟨F, inferInstance, b, hs, 2 * Real.log C,
    mul_nonneg (by norm_num) (Real.log_nonneg hC), ?_⟩
  intro n
  calc
    _ ≤ 2 * ((n : ℝ) + 1) * Real.log C := hbound n
    _ = _ := by ring

end StrictEUnit
