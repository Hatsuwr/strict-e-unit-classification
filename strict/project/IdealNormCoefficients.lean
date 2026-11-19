import TotalIdealCounting
import Mathlib.NumberTheory.LSeries.SumCoeff

noncomputable section
open scoped NumberField Topology nonZeroDivisors BigOperators
open NumberField Filter Finset Asymptotics
namespace StrictEUnit

def idealNormCoefficient (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n}

theorem finite_idealNorm_fiber (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    Finite {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = n} := by
  letI := finite_nonzeroIdeals_norm_le K (n : ℝ)
  apply Finite.of_injective (fun I => (⟨I.val, by exact_mod_cast I.prop.le⟩ :
    {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ n}))
  intro I J h
  exact Subtype.ext (congrArg (fun z :
    {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ n} => z.val) h)

theorem idealNormCoefficient_partial_sum (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    ∑ k ∈ Icc 1 n, idealNormCoefficient K k =
      Nat.card {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ n} := by
  classical
  letI (k : ℕ) := finite_idealNorm_fiber K k
  let e : {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ n} ≃
      Σ k : ↥(Icc 1 n), {I : (Ideal (𝓞 K))⁰ | Ideal.absNorm (I : Ideal (𝓞 K)) = k.val} :=
    { toFun := fun I => ⟨⟨Ideal.absNorm (I.val : Ideal (𝓞 K)), mem_Icc.mpr ⟨
        Ideal.absNorm_pos_of_nonZeroDivisors I.val, by exact_mod_cast I.prop⟩⟩, ⟨I.val, rfl⟩⟩
      invFun := fun x => ⟨x.2.val, by exact_mod_cast (x.2.prop ▸ (mem_Icc.mp x.1.prop).2)⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨⟨k, hk⟩, I, he⟩
        cases he
        rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  exact (Finset.sum_coe_sort (Icc 1 n) (idealNormCoefficient K)).symm

theorem totalIdealCount_mono (K : Type*) [Field K] [NumberField K]
    {c d : ℝ} (h : c ≤ d) :
    Nat.card {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} ≤
    Nat.card {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ d} := by
  letI := finite_nonzeroIdeals_norm_le K d
  exact Nat.card_le_card_of_injective
    (fun I => ⟨I.val, I.prop.trans h⟩)
    (fun I J h => Subtype.ext (congrArg (fun z :
      {I : (Ideal (𝓞 K))⁰ | (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ d} => z.val) h))

theorem totalIdealCount_global_linear_bound (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c →
      (Nat.card {I : (Ideal (𝓞 K))⁰ |
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ C * c := by
  obtain ⟨C, hC⟩ := totalIdealCount_linear_bound K
  obtain ⟨B, hB⟩ := eventually_atTop.mp hC
  let A : ℝ := Nat.card {I : (Ideal (𝓞 K))⁰ |
    (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ B}
  have hA : 0 ≤ A := Nat.cast_nonneg _
  refine ⟨max C A, hA.trans (le_max_right _ _), ?_⟩
  intro c hc
  by_cases h : B ≤ c
  · exact (hB c h).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
  · have hcount : (Nat.card {I : (Ideal (𝓞 K))⁰ |
        (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ A := by
      dsimp [A]
      exact_mod_cast totalIdealCount_mono K (le_of_not_ge h)
    exact hcount.trans ((le_mul_of_one_le_right hA hc).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)))

end StrictEUnit
end
