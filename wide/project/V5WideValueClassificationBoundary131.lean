import V5WideValueNormalization131

noncomputable section
namespace StrictEUnit

/-- Numerical wide E-value membership at algebraic arguments. -/
def V5IsWideEValue131 (u : ℂ) : Prop :=
  ∃ f : ℂ → ℂ, V5IsBroadEFunction f ∧ ∃ a : AlgebraicComplex, f a = u

/-- The numerical unit condition, independently of a subring packaging. -/
def V5IsWideEValueUnit131 (u : ℂ) : Prop :=
  u ≠ 0 ∧ V5IsWideEValue131 u ∧ V5IsWideEValue131 u⁻¹

theorem v5_wide_evalue_iff_at_one131 (u : ℂ) :
    V5IsWideEValue131 u ↔ ∃ f : ℂ → ℂ, V5IsBroadEFunction f ∧ f 1 = u := by
  constructor
  · rintro ⟨f,hf,a,ha⟩
    exact ⟨fun z => f ((a : ℂ) * z), v5_broad_function_rescale131 hf a,
      by simpa only [mul_one] using ha⟩
  · rintro ⟨f,hf,he⟩
    exact ⟨f,hf,1,by simpa only [IntermediateField.coe_one] using he⟩

theorem v5_wide_eunit_reverse131 {u : ℂ}
    (hu : ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
      u = α * Complex.exp β) : V5IsWideEValueUnit131 u := by
  obtain ⟨hne,h,h'⟩ := algebraic_exponential_reverse_inclusion hu
  have inc {x : ℂ} : IsStrictEValue x → V5IsWideEValue131 x := by
    rintro ⟨f,hf,a,ha⟩
    exact ⟨f, v5_strict_is_broad hf, a, ha⟩
  exact ⟨hne,inc h,inc h'⟩

/-- Interface for the one still-open forward result at normalized arguments. -/
def V5WideReciprocalAtOne131 : Prop :=
  ∀ {f g : ℂ → ℂ}, V5IsBroadEFunction f → V5IsBroadEFunction g →
    f 1 * g 1 = 1 →
    ∃ α β : AlgebraicComplex, α ≠ 0 ∧ f 1 = (α : ℂ) * Complex.exp (β : ℂ)

/-- Once the normalized reciprocal theorem is proved, no further arithmetic
or case splitting is needed to get the iff at all algebraic arguments. -/
theorem v5_wide_eunit_iff_of_at_one131 (hforward : V5WideReciprocalAtOne131) (u : ℂ) :
    V5IsWideEValueUnit131 u ↔
      ∃ α β : ℂ, IsAlgebraic ℚ α ∧ α ≠ 0 ∧ IsAlgebraic ℚ β ∧
        u = α * Complex.exp β := by
  constructor
  · rintro ⟨hne,hu,hui⟩
    obtain ⟨f,hf,hfu⟩ := (v5_wide_evalue_iff_at_one131 u).mp hu
    obtain ⟨g,hg,hgui⟩ := (v5_wide_evalue_iff_at_one131 u⁻¹).mp hui
    have hr : f 1 * g 1 = 1 := by rw [hfu,hgui,mul_inv_cancel₀ hne]
    obtain ⟨α,β,hα,he⟩ := hforward hf hg hr
    exact ⟨α,β,mem_algebraicClosure_iff.mp α.property,
      fun hz => hα (Subtype.ext hz), mem_algebraicClosure_iff.mp β.property, hfu.symm.trans he⟩
  · exact v5_wide_eunit_reverse131

end StrictEUnit
#print axioms StrictEUnit.v5_wide_evalue_iff_at_one131
#print axioms StrictEUnit.v5_wide_eunit_reverse131
#print axioms StrictEUnit.v5_wide_eunit_iff_of_at_one131
