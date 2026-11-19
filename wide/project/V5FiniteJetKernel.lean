import V5BroadDivisionAtOne
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A linear functional vanishing on a finite matrix kernel is a linear
combination of its literal rows. -/
theorem v5_finite_kernel_coordinate_combination
    {K : Type*} [Field K] {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    (M : I → J → K) (j₀ : J)
    (h : ∀ u : J → K, (∀ i, ∑ j, M i j * u j = 0) → u j₀ = 0) :
    ∃ w : I → K, ∀ j,
      ∑ i, w i * M i j = if j = j₀ then 1 else 0 := by
  classical
  let A : I → (J → K) →ₗ[K] K := fun i => ∑ j, M i j • LinearMap.proj j
  let B : (J → K) →ₗ[K] K := LinearMap.proj j₀
  have hs : (⨅ i, LinearMap.ker (A i)) ≤ LinearMap.ker B := by
    intro u hu
    apply LinearMap.mem_ker.mpr
    apply h u
    intro i
    have hi := LinearMap.mem_ker.mp ((Submodule.mem_iInf _).mp hu i)
    simpa only [A, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul] using hi
  obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (mem_span_of_iInf_ker_le_ker hs)
  refine ⟨w,fun j => ?_⟩
  have hj := LinearMap.congr_fun hw (Pi.single j (1:K))
  simp only [A, B, LinearMap.coeFn_sum, Finset.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul] at hj
  simp only [Finset.sum_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hj
  simpa only [eq_comm (a := j₀) (b := j)] using hj

/-- Only finite algebraic identities transfer between embeddings. No
continuity of the field maps is required. -/
theorem v5_finite_kernel_coordinate_across_maps
    {K L₁ L₂ : Type*} [Field K] [Field L₁] [Field L₂]
    {I J : Type*} [Fintype I] [Fintype J]
    (φ : K →+* L₁) (ψ : K →+* L₂) (M : I → J → K) (j₀ : J)
    (h : ∀ u : J → L₁, (∀ i, ∑ j, φ (M i j) * u j = 0) → u j₀ = 0)
    (u : J → L₂) (hu : ∀ i, ∑ j, ψ (M i j) * u j = 0) : u j₀ = 0 := by
  classical
  have hk (v : J → K) (hv : ∀ i, ∑ j, M i j * v j = 0) : v j₀ = 0 := by
    apply φ.injective
    rw [map_zero]
    apply h (fun j => φ (v j))
    intro i
    simpa only [map_sum, map_mul, map_zero] using congrArg φ (hv i)
  obtain ⟨w,hw⟩ := v5_finite_kernel_coordinate_combination M j₀ hk
  have h' (j : J) :
      ∑ i, ψ (w i) * ψ (M i j) = if j = j₀ then 1 else 0 := by
    by_cases hj : j = j₀ <;> simpa [map_sum, map_mul, hj] using congrArg ψ (hw j)
  calc
    u j₀ = ∑ j, (if j = j₀ then 1 else 0) * u j := by simp
    _ = ∑ j, (∑ i, ψ (w i) * ψ (M i j)) * u j := by simp only [h']
    _ = ∑ i, ψ (w i) * (∑ j, ψ (M i j) * u j) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    _ = 0 := by simp only [hu, mul_zero, Finset.sum_const_zero]

/-- An arbitrary finite initial vector, followed by all later coefficients
determined by a triangular recurrence with a chosen diagonal. -/
def v5ExtendJet {K : Type*} [Field K] {N : ℕ} (v : Fin N → K)
    (d : ℕ → K) (A : ℕ → ℕ → K) (n : ℕ) : K :=
  if hn : n < N then v ⟨n,hn⟩
  else (∑ j : Fin n, A n j.val * v5ExtendJet v d A j.val) / d n
termination_by n
decreasing_by exact j.isLt

theorem v5_extendJet_initial {K : Type*} [Field K] {N : ℕ} (v : Fin N → K)
    (d : ℕ → K) (A : ℕ → ℕ → K) (j : Fin N) :
    v5ExtendJet v d A j.val = v j := by
  rw [v5ExtendJet, dif_pos j.isLt]

theorem v5_extendJet_recurrence {K : Type*} [Field K] {N : ℕ} (v : Fin N → K)
    (d : ℕ → K) (A : ℕ → ℕ → K) (n : ℕ)
    (hn : N ≤ n) (hd : d n ≠ 0) :
    d n * v5ExtendJet v d A n = ∑ j : Fin n, A n j.val * v5ExtendJet v d A j.val := by
  conv_lhs => rw [v5ExtendJet, dif_neg (not_lt_of_ge hn)]
  rw [mul_comm, div_mul_cancel₀ _ hd]

/-- The exact kernel is the set of finite initial vectors of solutions of
the infinite initial-plus-triangular equations. -/
def V5JetSolution {K : Type*} [Field K] {N : ℕ} {I : Type*} [Fintype I]
    (M : I → Fin N → K) (d : ℕ → K) (A : ℕ → ℕ → K) (u : ℕ → K) : Prop :=
  (∀ i, ∑ j : Fin N, M i j * u j.val = 0) ∧
  (∀ n, N ≤ n → d n * u n = ∑ j : Fin n, A n j.val * u j.val)

theorem v5_exact_finite_jet_kernel {K : Type*} [Field K] {N : ℕ}
    {I : Type*} [Fintype I] (M : I → Fin N → K) (d : ℕ → K) (A : ℕ → ℕ → K)
    (hd : ∀ n, N ≤ n → d n ≠ 0) (v : Fin N → K) :
    (∀ i, ∑ j, M i j * v j = 0) ↔
    ∃! u : ℕ → K, V5JetSolution M d A u ∧ ∀ j : Fin N, u j.val = v j := by
  constructor
  · intro hv
    refine ⟨v5ExtendJet v d A,⟨⟨?_,fun n hn => v5_extendJet_recurrence v d A n hn (hd n hn)⟩,
      v5_extendJet_initial v d A⟩,?_⟩
    · intro i
      simpa only [v5_extendJet_initial] using hv i
    · intro u hu
      funext n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n < N
        · exact (hu.2 ⟨n,hn⟩).trans (v5_extendJet_initial v d A ⟨n,hn⟩).symm
        · have hn' := Nat.le_of_not_gt hn
          apply mul_left_cancel₀ (hd n hn')
          rw [hu.1.2 n hn', v5_extendJet_recurrence v d A n hn' (hd n hn')]
          exact Finset.sum_congr rfl (fun j _ => by rw [ih _ j.isLt])
  · rintro ⟨u,⟨hu,hv⟩,_⟩ i
    simpa only [hv] using hu.1 i

/-- If the original formal solution space has zero at a selected initial
coordinate, then so does the exact formal space after any coefficient map. -/
theorem v5_jet_solution_coordinate_across_maps
    {K L₁ L₂ : Type*} [Field K] [Field L₁] [Field L₂]
    {N : ℕ} {I : Type*} [Fintype I]
    (φ : K →+* L₁) (ψ : K →+* L₂) (M : I → Fin N → K) (d : ℕ → K) (A : ℕ → ℕ → K)
    (hdiag : ∀ n, N ≤ n → d n ≠ 0) (j₀ : Fin N)
    (h : ∀ u, V5JetSolution (fun i j => φ (M i j)) (fun n => φ (d n))
      (fun n j => φ (A n j)) u → u j₀.val = 0)
    (u : ℕ → L₂)
    (hu : V5JetSolution (fun i j => ψ (M i j)) (fun n => ψ (d n))
      (fun n j => ψ (A n j)) u) : u j₀.val = 0 := by
  apply v5_finite_kernel_coordinate_across_maps φ ψ M j₀ ?_
    (fun j => u j.val) hu.1
  intro v hv
  obtain ⟨U,⟨hU,hvU⟩,_⟩ := (v5_exact_finite_jet_kernel
    (fun i j => φ (M i j)) (fun n => φ (d n)) (fun n j => φ (A n j))
    (fun n hn => (map_ne_zero_iff φ φ.injective).mpr (hdiag n hn)) v).mp hv
  exact (hvU j₀).symm.trans (h U hU)

#print axioms v5_finite_kernel_coordinate_combination
#print axioms v5_finite_kernel_coordinate_across_maps
#print axioms v5_exact_finite_jet_kernel
#print axioms v5_jet_solution_coordinate_across_maps
end StrictEUnit
end
