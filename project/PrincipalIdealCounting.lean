import FundamentalConeCounting

noncomputable section
open scoped NumberField Topology nonZeroDivisors
open NumberField MeasureTheory Filter
namespace StrictEUnit

def mixedConeCount (K : Type*) [Field K] [NumberField K] (c : ℝ) : ℕ :=
  Nat.card {x : mixedEmbedding.mixedSpace K |
    x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x ≤ c ∧
    x ∈ mixedEmbedding.integerLattice K}

theorem mixedConeCount_eq_euclidean
    (K : Type*) [Field K] [NumberField K] (c : ℝ) :
    mixedConeCount K c =
      Nat.card ({x : mixedEmbedding.euclidean.mixedSpace K |
        mixedEmbedding.euclidean.toMixed K x ∈ mixedEmbedding.fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding.euclidean.toMixed K x) ≤ c} ∩
        mixedEmbedding.euclidean.integerLattice K :
          Set (mixedEmbedding.euclidean.mixedSpace K)) := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (mixedEmbedding.euclidean.toMixed K).symm.toEquiv
  intro x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  change (x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x ≤ c ∧
    x ∈ mixedEmbedding.integerLattice K) ↔
    ((mixedEmbedding.euclidean.toMixed K ((mixedEmbedding.euclidean.toMixed K).symm x) ∈
      mixedEmbedding.fundamentalCone K ∧
      mixedEmbedding.norm (mixedEmbedding.euclidean.toMixed K
        ((mixedEmbedding.euclidean.toMixed K).symm x)) ≤ c) ∧
      mixedEmbedding.euclidean.toMixed K ((mixedEmbedding.euclidean.toMixed K).symm x) ∈
        mixedEmbedding.integerLattice K)
  simp only [ContinuousLinearEquiv.apply_symm_apply, and_assoc]

theorem mixedConeCount_linear_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ᶠ c : ℝ in atTop, (mixedConeCount K c : ℝ) ≤ C * c := by
  obtain ⟨C, hC⟩ := fundamentalCone_lattice_count_linear_bound K
  refine ⟨C, ?_⟩
  filter_upwards [hC] with c hc
  rwa [mixedConeCount_eq_euclidean]

theorem principalIdealCount_mul_torsion
    (K : Type*) [Field K] [NumberField K] (c : ℝ) :
    Nat.card {I : (Ideal (𝓞 K))⁰ |
      (I : Ideal (𝓞 K)).IsPrincipal ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} *
      NumberField.Units.torsionOrder K = mixedConeCount K c := by
  have h := mixedEmbedding.fundamentalCone.card_isPrincipal_dvd_norm_le K (1 : (Ideal (𝓞 K))⁰) c
  simp only [OneMemClass.coe_one, one_dvd, true_and] at h
  refine h.trans ?_
  apply Nat.card_congr
  let e : {a : mixedEmbedding.fundamentalCone.idealSet K (1 : (Ideal (𝓞 K))⁰) |
      mixedEmbedding.norm (a : mixedEmbedding.mixedSpace K) ≤ c} ≃
      {x : mixedEmbedding.mixedSpace K |
        x ∈ mixedEmbedding.fundamentalCone K ∧ mixedEmbedding.norm x ≤ c ∧
        x ∈ mixedEmbedding.integerLattice K} :=
    { toFun := fun a => ⟨a.1.val, (mixedEmbedding.fundamentalCone.mem_idealSet.mp a.1.prop).1,
        a.2, by
          obtain ⟨z, _, hz⟩ := (mixedEmbedding.fundamentalCone.mem_idealSet.mp a.1.prop).2
          exact ⟨z, hz⟩⟩
      invFun := fun x => ⟨⟨x.val, mixedEmbedding.fundamentalCone.mem_idealSet.mpr
        ⟨x.2.1, by
          obtain ⟨z, hz⟩ := x.2.2.2
          exact ⟨z, by simp, hz⟩⟩⟩, x.2.2.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact e

theorem principalIdealCount_linear_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ᶠ c : ℝ in atTop,
      (Nat.card {I : (Ideal (𝓞 K))⁰ |
        (I : Ideal (𝓞 K)).IsPrincipal ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c} : ℝ) ≤ C * c := by
  obtain ⟨C, hC⟩ := mixedConeCount_linear_bound K
  refine ⟨C, ?_⟩
  filter_upwards [hC] with c hc
  have ht : 1 ≤ (Units.torsionOrder K : ℕ) := (Units.torsionOrder K).pos
  have hle := Nat.mul_le_mul_left
    (Nat.card {I : (Ideal (𝓞 K))⁰ |
      (I : Ideal (𝓞 K)).IsPrincipal ∧ (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) ≤ c}) ht
  rw [Nat.mul_one, principalIdealCount_mul_torsion] at hle
  exact (Nat.cast_le.mpr hle).trans hc

end StrictEUnit
end
