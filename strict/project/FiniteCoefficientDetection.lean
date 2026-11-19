import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Lattice.Fold

/-!
NEW SOURCE-ONLY: finite coefficient detection from actual separation.
No finite-jet injectivity or bounded-order premise is assumed. The proof chooses
a finite intersection of kernels with minimum dimension, then proves that it
already lies in every kernel. No characteristic-zero hypothesis is needed.
-/
noncomputable section
namespace StrictEUnit

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- A separating family of linear forms on a finite-dimensional space has a
finite separating subfamily, selected from the SAME forms. -/
theorem exists_finset_linearForm_detection [FiniteDimensional K V]
    (c : I → V →ₗ[K] K)
    (hsep : ∀ x : V, (∀ i, c i x = 0) → x = 0) :
    ∃ s : Finset I, ∀ x : V, (∀ i ∈ s, c i x = 0) → x = 0 := by
  classical
  let W (s : Finset I) : Submodule K V := ⨅ i ∈ s, LinearMap.ker (c i)
  have hmem (s : Finset I) (x : V) :
      x ∈ W s ↔ ∀ i ∈ s, c i x = 0 := by
    simp only [W, Submodule.mem_iInf, LinearMap.mem_ker]
  have hex : ∃ n : ℕ, ∃ s : Finset I, Module.finrank K (W s) = n :=
    ⟨Module.finrank K (W ∅), ∅, rfl⟩
  obtain ⟨s, hs⟩ := Nat.find_spec hex
  have hmin (t : Finset I) : Module.finrank K (W s) ≤ Module.finrank K (W t) := by
    rw [hs]
    exact Nat.find_min' hex ⟨t, rfl⟩
  refine ⟨s, fun x hx => hsep x (fun i => ?_)⟩
  have hle : W (insert i s) ≤ W s := by
    intro y hy
    exact (hmem s y).2 (fun j hj =>
      (hmem (insert i s) y).1 hy j (Finset.mem_insert_of_mem hj))
  have heq : W (insert i s) = W s :=
    Submodule.eq_of_le_of_finrank_le hle (hmin (insert i s))
  have hxi : x ∈ W (insert i s) := by
    rw [heq]
    exact (hmem s x).2 hx
  exact (hmem (insert i s) x).1 hxi i (Finset.mem_insert_self i s)

/-- For natural-indexed separating coefficients, a literal initial segment
suffices. The zero space is allowed; the chosen length is always positive. -/
theorem exists_initial_linearForm_detection [FiniteDimensional K V]
    (c : ℕ → V →ₗ[K] K)
    (hsep : ∀ x : V, (∀ n, c n x = 0) → x = 0) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : V, (∀ n < N, c n x = 0) → x = 0 := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_linearForm_detection c hsep
  refine ⟨s.sup id + 1, Nat.succ_pos _, fun x hx => hs x (fun n hn => ?_)⟩
  exact hx n (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))

end StrictEUnit
end
