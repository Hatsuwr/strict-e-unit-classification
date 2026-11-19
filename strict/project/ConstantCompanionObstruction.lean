import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Row-oriented constant companion, of positive size n+1. -/
def constantCompanion (n : ℕ) (t : K) (v : Fin (n+1) → K) :
    Matrix (Fin (n+1)) (Fin (n+1)) K :=
  Fin.lastCases v (fun i => Pi.single i.succ t)

theorem constantCompanion_row_action (n : ℕ) (t : K) (v x : Fin (n+1) → K) :
    (x ᵥ* constantCompanion n t v) 0 = x (Fin.last n)*v 0 ∧
    ∀ j : Fin n, (x ᵥ* constantCompanion n t v) j.succ =
      x j.castSucc*t + x (Fin.last n)*v j.succ := by
  classical
  constructor
  · change (∑ i, x i * constantCompanion n t v i 0) = _
    rw [Fin.sum_univ_castSucc]
    simp [constantCompanion, Pi.single_apply, Fin.ext_iff]
  · intro j
    change (∑ i, x i * constantCompanion n t v i j.succ) = _
    rw [Fin.sum_univ_castSucc]
    simp [constantCompanion, Pi.single_apply, Fin.succ_inj, eq_comm]

/-- The tail beginning at the least nonzero last-row entry is invariant and
has no nonzero vector killed by one row action. -/
theorem constantCompanion_tail (n : ℕ) (t : K) (ht : t ≠ 0)
    (v : Fin (n+1) → K) (k : Fin (n+1)) (hk : v k ≠ 0)
    (hv : ∀ j, j.val < k.val → v j = 0)
    (x : Fin (n+1) → K) (hx : ∀ j, j.val < k.val → x j = 0) :
    (∀ j, j.val < k.val → (x ᵥ* constantCompanion n t v) j = 0) ∧
    (x ᵥ* constantCompanion n t v = 0 → x = 0) := by
  have ha := constantCompanion_row_action n t v x
  constructor
  · intro j hj
    cases j using Fin.cases with
    | zero => rw [ha.1, hv 0 hj, mul_zero]
    | succ j =>
      rw [ha.2, hx j.castSucc (by simpa using Nat.lt_trans (Nat.lt_succ_self j.val) hj),
        hv j.succ hj, zero_mul, mul_zero, add_zero]
  · intro hz
    have hlast : x (Fin.last n) = 0 := by
      have he := congrFun hz k
      cases k using Fin.cases with
      | zero =>
        rw [ha.1] at he
        exact (mul_eq_zero.mp he).resolve_right hk
      | succ k =>
        rw [ha.2, hx k.castSucc (by simp), zero_mul, zero_add] at he
        exact (mul_eq_zero.mp he).resolve_right hk
    funext i
    cases i using Fin.lastCases with
    | last => exact hlast
    | cast i =>
      have he := congrFun hz i.succ
      rw [ha.2, hlast, zero_mul, add_zero] at he
      exact (mul_eq_zero.mp he).resolve_right ht

theorem constantCompanion_initial_orbit (n : ℕ) (t : K)
    (v : Fin (n+1) → K) (j : ℕ) (hj : j ≤ n) :
    (fun x => x ᵥ* constantCompanion n t v)^[j] (Pi.single 0 1) =
      Pi.single ⟨j,by omega⟩ (t^j) := by
  classical
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), Matrix.single_vecMul]
    have he : (⟨j,by omega⟩ : Fin (n+1)) = (⟨j,by omega⟩ : Fin n).castSucc := rfl
    rw [he]
    simp only [constantCompanion, Fin.lastCases_castSucc]
    funext i
    simp [Pi.single_apply, Pi.smul_apply, smul_eq_mul, pow_succ, mul_comm]

/-- No eventual-zero orbit is possible when the last row is nonzero. No
algebraic closure, characteristic restriction or spectral theorem is used. -/
theorem constantCompanion_orbit_not_eventually_zero (n : ℕ) (t : K) (ht : t ≠ 0)
    (v : Fin (n+1) → K) (hv : ∃ i, v i ≠ 0) :
    ¬ ∃ N, ∀ m, N ≤ m →
      (fun x => x ᵥ* constantCompanion n t v)^[m] (Pi.single 0 1) = 0 := by
  classical
  have hex : ∃ j : ℕ, ∃ hj : j < n+1, v ⟨j,hj⟩ ≠ 0 := by
    obtain ⟨i,hi⟩ := hv
    exact ⟨i.val,i.isLt,hi⟩
  let k : Fin (n+1) := ⟨Nat.find hex,(Nat.find_spec hex).choose⟩
  have hk : v k ≠ 0 := (Nat.find_spec hex).choose_spec
  have hlow : ∀ j, j.val < k.val → v j = 0 := by
    intro j hj
    by_contra h
    exact Nat.find_min hex hj ⟨j.isLt,h⟩
  let S := fun x => x ᵥ* constantCompanion n t v
  let x0 : Fin (n+1) → K := Pi.single k (t^k.val)
  have hx0 : x0 ≠ 0 := by
    intro h
    have he := congrFun h k
    have hp := pow_ne_zero k.val ht
    exact hp (by simpa [x0] using he)
  have htail0 : ∀ j, j.val < k.val → x0 j = 0 := by
    intro j hj
    have hne : j ≠ k := by intro h; subst j; omega
    simp [x0, Pi.single_apply, hne, Ne.symm hne]
  have hinv : ∀ m, (∀ j, j.val < k.val → (S^[m] x0) j = 0) ∧ S^[m] x0 ≠ 0 := by
    intro m
    induction m with
    | zero => exact ⟨htail0,hx0⟩
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      have hh := constantCompanion_tail n t ht v k hk hlow (S^[m] x0) ih.1
      exact ⟨hh.1,fun hz => ih.2 (hh.2 hz)⟩
  rintro ⟨N,hN⟩
  have he := hN (N+k.val) (by omega)
  rw [Function.iterate_add_apply,
    constantCompanion_initial_orbit n t v k.val (by omega)] at he
  exact (hinv N).2 he

theorem constantCompanion_apply (n : ℕ) (t : K) (v : Fin (n+1) → K)
    (i j : Fin (n+1)) :
    constantCompanion n t v i j =
      if i.val+1 < n+1 then (if j.val = i.val+1 then t else 0) else v j := by
  classical
  cases i using Fin.lastCases with
  | last => simp [constantCompanion]
  | cast i =>
    have hi : i.val+1 < n+1 := by omega
    simp [constantCompanion, hi, Pi.single_apply, Fin.ext_iff, eq_comm]

theorem constantCompanion_orbit_eq_power (n : ℕ) (t : K)
    (v : Fin (n+1) → K) (m : ℕ) :
    (fun x => x ᵥ* constantCompanion n t v)^[m] (Pi.single 0 1) =
      Pi.single 0 1 ᵥ* (constantCompanion n t v)^m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Matrix.vecMul_vecMul, pow_succ]

theorem constantCompanion_power_not_eventually_zero (n : ℕ) (t : K) (ht : t ≠ 0)
    (v : Fin (n+1) → K) (hv : ∃ i, v i ≠ 0) :
    ¬ ∃ N, ∀ m, N ≤ m → Pi.single 0 1 ᵥ* (constantCompanion n t v)^m = 0 := by
  simpa only [constantCompanion_orbit_eq_power] using
    constantCompanion_orbit_not_eventually_zero n t ht v hv

end StrictEUnit
end
