import IntegralClearedDualColumn

/-!
# One literal common matrix for a simultaneous finite cutoff

The input polynomial rows represent T^j times the jth divided dual column,
only through s+r-1. Their existence/integrality and nonzero determinant remain
explicit separate gaps. The conclusion constructs B_n; it does not assume the
cleared connection product is polynomial.
-/

noncomputable section

open scoped BigOperators Matrix

namespace StrictEUnit

/-- For every n≤s, the SAME M with columns Q_0,...,Q_(r-1) satisfies
H_n*M = map(B_n), where H_n = T^n*A_n/n!. No rank or T(0) premise is used. -/
theorem exists_common_dual_matrix_polynomial_products
    {k R F : Type*} [Field k] [CharZero k] [CommRing R]
    [Field F] [CharZero F] [Algebra k F]
    (ι : Polynomial R →+* F) (d : Derivation k F F)
    (hcompat : ∀ Q : Polynomial R, d (ι Q) = ι Q.derivative)
    (T : Polynomial R) (hT : ι T ≠ 0)
    {r : ℕ} (A : Matrix (Fin r) (Fin r) F) (P : Fin r → F)
    (Q : ℕ → Fin r → Polynomial R) (s : ℕ)
    (hQ : ∀ l : ℕ, l ≤ s + r - 1 → ∀ i : Fin r,
      ι (Q l i) = (ι T)^l * dualDividedColumn (matrixDualColumn d A) P l i) :
    ∀ n : ℕ, n ≤ s → ∃ B : Matrix (Fin r) (Fin r) (Polynomial R),
      Matrix.of (fun i l : Fin r => (ι T)^n * matrixConnectionSequence d A n i l / (n.factorial : F)) *
        Matrix.of (fun l j : Fin r => ι (Q j.val l)) = B.map ι := by
  classical
  intro n hn
  have hentry (i j : Fin r) :
      (Matrix.of (fun i l : Fin r => (ι T)^n * matrixConnectionSequence d A n i l / (n.factorial : F)) *
        Matrix.of (fun l j : Fin r => ι (Q j.val l))) i j ∈ ι.range := by
    have hj : j.val < r := j.isLt
    have hcut : n + j.val ≤ s + r - 1 := by omega
    have hcol := cleared_dual_column_mem_polynomial_range
      ι d hcompat T hT A P Q n j.val
      (fun l hl i => hQ l (hl.trans hcut) i) i
    have hmap :
        (Matrix.of (fun i l : Fin r => (ι T)^n * matrixConnectionSequence d A n i l / (n.factorial : F)) *
          Matrix.of (fun l j : Fin r => ι (Q j.val l))) i j =
        (ι T)^(n + j.val) * (∑ l : Fin r, matrixConnectionSequence d A n i l *
          dualDividedColumn (matrixDualColumn d A) P j.val l) / (n.factorial : F) := by
      change (∑ l : Fin r,
        ((ι T)^n * matrixConnectionSequence d A n i l / (n.factorial : F)) *
          ι (Q j.val l)) = _
      calc
        _ = ∑ l : Fin r, (ι T)^(n + j.val) *
            (matrixConnectionSequence d A n i l *
              dualDividedColumn (matrixDualColumn d A) P j.val l) / (n.factorial : F) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [hQ j.val (by omega) l, pow_add]
          ring
        _ = _ := by rw [← Finset.sum_div, ← Finset.mul_sum]
    rw [hmap]
    exact hcol
  have hex : ∀ i j : Fin r, ∃ b : Polynomial R,
      ι b = (Matrix.of (fun i l : Fin r => (ι T)^n * matrixConnectionSequence d A n i l /
        (n.factorial : F)) * Matrix.of (fun l j : Fin r => ι (Q j.val l))) i j := by
    intro i j
    exact (RingHom.mem_range).mp (hentry i j)
  let B : Matrix (Fin r) (Fin r) (Polynomial R) := fun i j => Classical.choose (hex i j)
  refine ⟨B, ?_⟩
  apply Matrix.ext
  intro i j
  exact (Classical.choose_spec (hex i j)).symm

end StrictEUnit

end
