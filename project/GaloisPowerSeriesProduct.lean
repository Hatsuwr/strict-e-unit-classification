import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.PowerSeries.Basic

/-! A finite Galois permutation of factors makes every product coefficient
rational. No vanishing of conjugate factors or minimality transfer is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem powerSeries_prod_coeff_rational_of_permuted
    {K ι : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    [Fintype ι] (s : ι → PowerSeries K)
    (hperm : ∀ σ : K ≃ₐ[ℚ] K, ∃ e : Equiv.Perm ι,
      ∀ i, PowerSeries.map σ.toRingHom (s i) = s (e i)) (n : ℕ) :
    ∃ q : ℚ, algebraMap ℚ K q = PowerSeries.coeff K n (∏ i, s i) := by
  classical
  have hprod (σ : K ≃ₐ[ℚ] K) :
      PowerSeries.map σ.toRingHom (∏ i, s i) = ∏ i, s i := by
    obtain ⟨e, he⟩ := hperm σ
    simp only [map_prod, he]
    exact Equiv.prod_comp e s
  have hfixed : PowerSeries.coeff K n (∏ i, s i) ∈
      IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) := by
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro σ _
    have h := congrArg (PowerSeries.coeff K n) (hprod σ)
    simpa only [PowerSeries.coeff_map] using h
  have hbot : IntermediateField.fixedField (⊤ : Subgroup (K ≃ₐ[ℚ] K)) = ⊥ :=
    (IsGalois.tfae.out 0 1).mp (inferInstanceAs (IsGalois ℚ K))
  rw [hbot] at hfixed
  exact IntermediateField.mem_bot.mp hfixed

theorem powerSeries_conjugate_prod_coeff_rational
    {K : Type*} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (f : PowerSeries K) (n : ℕ) :
    ∃ q : ℚ, algebraMap ℚ K q = PowerSeries.coeff K n
      (∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom f) := by
  classical
  apply powerSeries_prod_coeff_rational_of_permuted _ _ n
  intro τ
  refine ⟨Equiv.mulLeft τ, ?_⟩
  intro σ
  ext k
  simp only [PowerSeries.coeff_map]
  rfl
end StrictEUnit
