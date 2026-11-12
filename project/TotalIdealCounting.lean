import IdealClassCounting
import Mathlib.NumberTheory.NumberField.ClassNumber

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Filter
namespace StrictEUnit

theorem finite_nonzeroIdeals_norm_le
    (K : Type*) [Field K] [NumberField K] (c : ℝ) :
    Finite {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} := by
  letI := (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) ⌈c⌉₊).to_subtype
  apply Finite.of_injective (fun I => (⟨I.val.val, by
    exact_mod_cast I.prop.trans (Nat.le_ceil c)⟩ :
    {J : Ideal (𝓞 K) | Ideal.absNorm J ≤ ⌈c⌉₊}))
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {J : Ideal (𝓞 K) | Ideal.absNorm J ≤ ⌈c⌉₊} => z.val) h

theorem idealCount_eq_sum_classes
    (K : Type*) [Field K] [NumberField K] (c : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} =
      ∑ g : ClassGroup (𝓞 K), Nat.card {I : (Ideal (𝓞 K))⁰ |
        ClassGroup.mk0 I = g ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} := by
  classical
  letI := finite_nonzeroIdeals_norm_le K c
  letI (g : ClassGroup (𝓞 K)) : Finite {I : (Ideal (𝓞 K))⁰ |
      ClassGroup.mk0 I = g ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} :=
    Finite.of_injective
      (fun I => (⟨I.val, I.prop.2⟩ :
        {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c}))
      (fun I J h => Subtype.ext (congrArg (fun z :
        {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} => z.val) h))
  let e : {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} ≃
    Σ g : ClassGroup (𝓞 K), {I : (Ideal (𝓞 K))⁰ |
        ClassGroup.mk0 I = g ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} :=
    { toFun := fun I => ⟨ClassGroup.mk0 I.val, ⟨I.val, rfl, I.prop⟩⟩
      invFun := fun x => ⟨x.2.val, x.2.prop.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨g, I, he, hb⟩
        cases he
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]

/-- Summing the independently established class bounds gives the actual
eventual linear count bound for all nonzero integral ideals. -/
theorem totalIdealCount_linear_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ᶠ c : ℝ in atTop,
      (Nat.card {I : (Ideal (𝓞 K))⁰ |
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ C * c := by
  classical
  have hclass : ∀ g : ClassGroup (𝓞 K), ∃ C : ℝ, ∀ᶠ c : ℝ in atTop,
      (Nat.card {I : (Ideal (𝓞 K))⁰ |
        ClassGroup.mk0 I = g ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ C * c := by
    intro g
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective g⁻¹
    simpa only [hJ, inv_inv] using idealClassCount_linear_bound K J
  choose C hC using hclass
  refine ⟨∑ g, C g, ?_⟩
  filter_upwards [Filter.eventually_all.mpr hC] with c hc
  rw [idealCount_eq_sum_classes, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun g _ => hc g)

end StrictEUnit
end
