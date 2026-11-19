import V5OrdinarySystemColumns
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace StrictEUnit
open scoped Topology BigOperators
open Filter

noncomputable def v5WeightedGerm {n : ℕ} (u : Fin n → ℂ → ℂ)
    (c : Fin n → ℂ) (z : ℂ) : ℂ :=
  ∑ j, c j * u j z

/-- Initial jets of the images of the original family under the right factor.
The input vector specifies the linear combination of those images. -/
noncomputable def v5FactorInitialJetMap {n : ℕ} (s : ℕ)
    (image : Fin n → ℂ → ℂ) (y : ℂ) : (Fin n → ℂ) →ₗ[ℂ] (Fin s → ℂ) where
  toFun c i := ∑ j, c j * iteratedDeriv i.val (image j) y
  map_add' a b := by
    funext i
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a b := by
    funext i
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem v5_finrank_initialJet_kernel_ge {n m : ℕ} (hm : m ≤ n)
    (J : (Fin n → ℂ) →ₗ[ℂ] (Fin (n - m) → ℂ)) :
    m ≤ Module.finrank ℂ (LinearMap.ker J) := by
  have hdim := J.finrank_range_add_finrank_ker
  have hrange := (LinearMap.range J).finrank_le
  simp only [Module.finrank_pi, Fintype.card_fin] at hdim hrange
  omega

theorem v5_exists_independent_initialJet_kernel {n m : ℕ} (hm : m ≤ n)
    (J : (Fin n → ℂ) →ₗ[ℂ] (Fin (n - m) → ℂ)) :
    ∃ c : Fin m → Fin n → ℂ, LinearIndependent ℂ c ∧ ∀ i, J (c i) = 0 := by
  obtain ⟨c, hc⟩ := exists_linearIndependent_of_le_finrank
    (v5_finrank_initialJet_kernel_ge hm J)
  exact ⟨fun i => (c i : Fin n → ℂ), hc.map' (LinearMap.ker J).subtype
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective), fun i => (c i).property⟩

theorem v5_weighted_germs_independent {n m : ℕ} {x : ℂ}
    {u : Fin n → ℂ → ℂ} (hu : v5FiniteGermIndependent x u)
    {a : Fin m → Fin n → ℂ} (ha : LinearIndependent ℂ a) :
    v5FiniteGermIndependent x (fun i => v5WeightedGerm u (a i)) := by
  classical
  intro c hc
  have hzero : ∀ j, (∑ i, c i * a i j) = 0 := by
    apply hu (fun j => ∑ i, c i * a i j)
    filter_upwards [hc] with z hz
    unfold v5WeightedGerm at hz
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum] at hz
    convert hz using 1
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  apply Fintype.linearIndependent_iff.mp ha c
  funext j
  change _ = (0 : ℂ)
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hzero j

/-- The only analytic premise left in this finite-dimensional selection step is
that zero initial jets of the right-factor images imply its marked germ equation. -/
theorem v5_extract_factor_family_by_initial_jets {K : Type*} [Field K] [Algebra K ℂ]
    {n m : ℕ} (hm : m ≤ n) {x : ℂ} (y : ℂ)
    (u image : Fin n → ℂ → ℂ) (hu : v5FiniteGermIndependent x u)
    (q : ℕ → Polynomial K)
    (hkernel : ∀ c : Fin n → ℂ, v5FactorInitialJetMap (n - m) image y c = 0 →
      ∀ᶠ z in 𝓝 x, v5RowResidual (v5WeightedGerm u c) m q z = 0) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent x v ∧
      ∀ i, ∀ᶠ z in 𝓝 x, v5RowResidual (v i) m q z = 0 := by
  obtain ⟨a, ha, hJ⟩ := v5_exists_independent_initialJet_kernel hm
    (v5FactorInitialJetMap (n - m) image y)
  exact ⟨fun i => v5WeightedGerm u (a i), v5_weighted_germs_independent hu ha,
    fun i => hkernel (a i) (hJ i)⟩

#print axioms v5_finrank_initialJet_kernel_ge
#print axioms v5_weighted_germs_independent
#print axioms v5_extract_factor_family_by_initial_jets
end StrictEUnit
