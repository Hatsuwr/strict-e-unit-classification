import PrincipalIdealCounting

noncomputable section
open scoped NumberField Topology nonZeroDivisors
open NumberField Filter
namespace StrictEUnit

theorem finite_principalIdeals_norm_le
    (K : Type*) [Field K] [NumberField K] (c : ℝ) :
    Finite {I : (Ideal (𝓞 K))⁰ |
      (I : Ideal (𝓞 K)).IsPrincipal ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} := by
  letI := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) ⌈c⌉₊).to_subtype
  apply Finite.of_injective (fun I => (⟨I.val.val, by
    exact_mod_cast I.prop.2.trans (Nat.le_ceil c)⟩ :
    {J : Ideal (𝓞 K) | Ideal.absNorm J ≤ ⌈c⌉₊}))
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {J : Ideal (𝓞 K) | Ideal.absNorm J ≤ ⌈c⌉₊} => z.val) h

/-- Multiplication by a representative of the inverse class injects one
ideal class into principal ideals, with the exact norm rescaling. -/
theorem idealClassCount_le_principal
    (K : Type*) [Field K] [NumberField K]
    (J : (Ideal (𝓞 K))⁰) (c : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ |
      ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} ≤
    Nat.card {I : (Ideal (𝓞 K))⁰ |
      (I : Ideal (𝓞 K)).IsPrincipal ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
          c * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)} := by
  letI := finite_principalIdeals_norm_le K (c * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ))
  let f : {I : (Ideal (𝓞 K))⁰ |
      ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} →
    {I : (Ideal (𝓞 K))⁰ |
      (I : Ideal (𝓞 K)).IsPrincipal ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤
          c * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ)} :=
    fun I => ⟨I.val * J, by
      apply (ClassGroup.mk0_eq_one_iff (I.val * J).prop).mp
      rw [map_mul, I.prop.1, inv_mul_cancel],
      by
        change (Ideal.absNorm ((I.val : Ideal (𝓞 K)) * (J : Ideal (𝓞 K))) : ℝ) ≤ _
        rw [map_mul, Nat.cast_mul]
        exact mul_le_mul_of_nonneg_right I.prop.2 (Nat.cast_nonneg _)⟩
  apply Nat.card_le_card_of_injective f
  intro I I' h
  apply Subtype.ext
  exact mul_right_cancel (congrArg Subtype.val h)

/-- Every individual ideal class has an eventual linear norm-count bound. -/
theorem idealClassCount_linear_bound
    (K : Type*) [Field K] [NumberField K] (J : (Ideal (𝓞 K))⁰) :
    ∃ C : ℝ, ∀ᶠ c : ℝ in atTop,
      (Nat.card {I : (Ideal (𝓞 K))⁰ |
        ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ∧
          (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ C * c := by
  obtain ⟨C, hC⟩ := principalIdealCount_linear_bound K
  have hpos : (0 : ℝ) < (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ) := by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors J
  have ht : Tendsto (fun c : ℝ => c * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ))
      atTop atTop := tendsto_id.atTop_mul_const hpos
  refine ⟨C * (Ideal.absNorm (J : Ideal (𝓞 K)) : ℝ), ?_⟩
  filter_upwards [ht.eventually hC] with c hc
  have hle : (Nat.card {I : (Ideal (𝓞 K))⁰ |
      ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ∧
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ _ :=
    Nat.cast_le.mpr (idealClassCount_le_principal K J c)
  calc
    _ ≤ _ := hle.trans hc
    _ = _ := by ring

end StrictEUnit
end
