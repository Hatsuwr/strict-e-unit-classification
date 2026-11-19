import FormalFundamentalMatrix

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Entrywise coefficient uniqueness for the literal left matrix ODE. -/
theorem v5_powerSeries_matrix_solution_unique
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A U V : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hU : U.map (PowerSeries.derivative K) = A * U)
    (hV : V.map (PowerSeries.derivative K) = A * V)
    (h0 : U.map (PowerSeries.constantCoeff K) = V.map (PowerSeries.constantCoeff K)) :
    U = V := by
  have hc : ∀ n i j, PowerSeries.coeff K n (U i j) = PowerSeries.coeff K n (V i j) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i j
      cases n with
      | zero =>
        simpa only [PowerSeries.coeff_zero_eq_constantCoeff, Matrix.map_apply] using
          congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j) h0
      | succ n =>
        have hu := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => PowerSeries.coeff K n (M i j)) hU
        have hv := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => PowerSeries.coeff K n (M i j)) hV
        simp only [Matrix.map_apply, PowerSeries.coeff_derivative, powerSeries_matrix_mul_coeff] at hu hv
        have hs : (∑ k : Fin (n+1), ∑ l : Fin r,
            PowerSeries.coeff K k.val (A i l) * PowerSeries.coeff K (n-k.val) (U l j)) =
          ∑ k : Fin (n+1), ∑ l : Fin r,
            PowerSeries.coeff K k.val (A i l) * PowerSeries.coeff K (n-k.val) (V l j) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [ih (n-k.val) (Nat.lt_succ_of_le (Nat.sub_le _ _)) l j]
        exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero n : (n+1 : K) ≠ 0)
          (hu.trans (hs.trans hv.symm))
  apply Matrix.ext
  intro i j
  exact PowerSeries.ext (fun n => hc n i j)

/-- A normalized solution is the actual recursively constructed frame. -/
theorem v5_eq_formalFundamentalMatrix
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A U : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hU : U.map (PowerSeries.derivative K) = A * U)
    (h0 : U.map (PowerSeries.constantCoeff K) = 1) :
    U = formalFundamentalMatrix A :=
  v5_powerSeries_matrix_solution_unique A U _ hU (formalFundamentalMatrix_derivative A)
    (h0.trans (formalFundamentalMatrix_constantCoeff A).symm)

/-- Scalar base change commutes with the formal ordinary derivative. -/
theorem v5_powerSeries_derivative_map
    {K L : Type*} [Field K] [Field L] (f : K →+* L) (p : PowerSeries K) :
    PowerSeries.derivative L (PowerSeries.map f p) =
      PowerSeries.map f (PowerSeries.derivative K p) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_map, map_mul, map_add, map_natCast, map_one]

/-- The actual recursively constructed normalized matrix commutes with
scalar base change, not merely an independently chosen solution frame. -/
theorem v5_formalFundamentalMatrix_map
    {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] {r : ℕ}
    (f : K →+* L) (A : Matrix (Fin r) (Fin r) (PowerSeries K)) :
    (formalFundamentalMatrix A).map (PowerSeries.map f) =
      formalFundamentalMatrix (A.map (PowerSeries.map f)) := by
  apply v5_eq_formalFundamentalMatrix
  · have hd := formalFundamentalMatrix_derivative A
    have hm := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) =>
      M.map (PowerSeries.map f)) hd
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries L) => M i j) hm
    simpa only [Matrix.map_apply, v5_powerSeries_derivative_map,
      Matrix.mul_apply, map_sum, map_mul] using hh
  · have h0 := formalFundamentalMatrix_constantCoeff A
    apply Matrix.ext
    intro i j
    have hh := congrArg (fun M : Matrix (Fin r) (Fin r) K => f (M i j)) h0
    simpa only [Matrix.map_apply, ← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_map, Matrix.one_apply, apply_ite f, map_one, map_zero] using hh

end StrictEUnit
#print axioms StrictEUnit.v5_powerSeries_matrix_solution_unique
#print axioms StrictEUnit.v5_eq_formalFundamentalMatrix
#print axioms StrictEUnit.v5_powerSeries_derivative_map
#print axioms StrictEUnit.v5_formalFundamentalMatrix_map
