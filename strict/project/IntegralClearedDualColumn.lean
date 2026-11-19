import MatrixDividedEntry
import ScaledQuotientHasse

/-! A single cleared dual column lies in the original polynomial-map range,
using only explicitly supplied representatives through the finite cutoff. -/

noncomputable section

open scoped BigOperators Matrix

namespace StrictEUnit

/-- This theorem does not construct the supplied polynomial rows. It proves
polynomiality of the cleared connection action from those finite row data and
the genuine shifted dual / quotient-Hasse identities. -/
theorem cleared_dual_column_mem_polynomial_range
    {k R F : Type*} [Field k] [CharZero k] [CommRing R]
    [Field F] [CharZero F] [Algebra k F]
    (ι : Polynomial R →+* F) (d : Derivation k F F)
    (hcompat : ∀ Q : Polynomial R, d (ι Q) = ι Q.derivative)
    (T : Polynomial R) (hT : ι T ≠ 0)
    {r : ℕ} (A : Matrix (Fin r) (Fin r) F) (P : Fin r → F)
    (Q : ℕ → Fin r → Polynomial R) (n j : ℕ)
    (hQ : ∀ l : ℕ, l ≤ n + j → ∀ i : Fin r,
      ι (Q l i) = (ι T)^l * dualDividedColumn (matrixDualColumn d A) P l i)
    (i : Fin r) :
    (ι T)^(n + j) * (∑ l : Fin r, matrixConnectionSequence d A n i l *
      dualDividedColumn (matrixDualColumn d A) P j l) / (n.factorial : F) ∈ ι.range := by
  have heq := congrArg (fun z : F => (ι T)^(n + j) * z)
    (matrix_connection_divided_shifted_entry d A n j P i)
  dsimp only at heq
  rw [Finset.mul_sum] at heq
  rw [mul_div_assoc, heq]
  apply ι.range.sum_mem
  intro h hh
  have hhN : h ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hindex : j + h ≤ n + j := by omega
  have hQdiv : dualDividedColumn (matrixDualColumn d A) P (j + h) i =
      ι (Q (j + h) i) / (ι T)^(j + h) := by
    apply (eq_div_iff (pow_ne_zero (j + h) hT)).mpr
    exact (mul_comm _ _).trans (hQ (j + h) hindex i).symm
  obtain ⟨U, hU⟩ := exists_polynomial_scaled_divided_quotient
    ι d hcompat T hT (Q (j + h) i) (j + h) (n - h)
  have hexp : (j + h) + (n - h) = n + j := by omega
  rw [hexp, ← hQdiv] at hU
  have hscalar : ((-1 : F)^h * ((j + h).choose h : F)) ∈ ι.range := by
    simpa only [map_mul, map_pow, map_neg, map_one, map_natCast] using
      ι.mem_range_self (((-1 : Polynomial R)^h) * ((j + h).choose h : Polynomial R))
  have hterm :
      (ι T)^(n + j) *
        (((-1 : F)^h * ((j + h).choose h : F)) *
          (d^[n - h]) (dualDividedColumn (matrixDualColumn d A) P (j + h) i) /
            ((n - h).factorial : F)) =
      ((-1 : F)^h * ((j + h).choose h : F)) * ι U := by
    rw [hU]
    ring
  rw [hterm]
  exact ι.range.mul_mem hscalar (ι.mem_range_self U)

end StrictEUnit

end
