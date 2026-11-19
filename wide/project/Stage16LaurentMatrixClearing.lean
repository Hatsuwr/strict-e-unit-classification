import Mathlib.Algebra.Polynomial.Laurent
import EntireTaylorEmbedding

/-!
Finite Laurent matrices admit one positive common clearing exponent. All Laurent
identities are evaluated at units, so no negative power is evaluated at zero.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Every finite Laurent matrix has an actual polynomial numerator after
multiplication by a common positive power of the coordinate. -/
theorem stage16_laurentMatrix_exists_positive_clearing
    {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n]
    (A : Matrix m n (LaurentPolynomial R)) :
    ∃ L : ℕ, 1 ≤ L ∧ ∃ P : Matrix m n (Polynomial R),
      ∀ i j, Polynomial.toLaurent (P i j) = A i j * LaurentPolynomial.T (L : ℤ) := by
  classical
  have h (i : m) (j : n) := LaurentPolynomial.exists_T_pow (A i j)
  choose N Q hQ using h
  let L := (Finset.univ.sup fun t : m × n => N t.1 t.2) + 1
  have hle (i : m) (j : n) : N i j ≤ L :=
    (Finset.le_sup (f := fun t : m × n => N t.1 t.2) (Finset.mem_univ (i,j))).trans
      (Nat.le_succ _)
  refine ⟨L, Nat.succ_le_succ (Nat.zero_le _),
    fun i j => Q i j * Polynomial.X ^ (L - N i j), ?_⟩
  intro i j
  rw [map_mul, Polynomial.toLaurent_X_pow, hQ, LaurentPolynomial.mul_T_assoc,
    ← Nat.cast_add, Nat.add_sub_of_le (hle i j)]

/-- Laurent evaluation is defined only at an actual unit. -/
def stage16_laurentEval (z : ℂˣ) : LaurentPolynomial ℂ →+* ℂ :=
  LaurentPolynomial.eval₂ (RingHom.id ℂ) z

@[simp] theorem stage16_laurentEval_toLaurent (z : ℂˣ) (P : Polynomial ℂ) :
    stage16_laurentEval z (Polynomial.toLaurent P) = P.eval (z : ℂ) := by
  exact LaurentPolynomial.eval₂_toLaurent (RingHom.id ℂ) z P

@[simp] theorem stage16_laurentEval_T_nat (z : ℂˣ) (L : ℕ) :
    stage16_laurentEval z (LaurentPolynomial.T (L : ℤ)) = (z : ℂ)^L :=
  LaurentPolynomial.eval₂_T_n (RingHom.id ℂ) z L

/-- The algebraic clearing identity is the actual analytic identity at every
nonzero complex point, using its canonical unit. -/
theorem stage16_laurent_clearing_eval (f : LaurentPolynomial ℂ)
    (P : Polynomial ℂ) (L : ℕ)
    (hP : Polynomial.toLaurent P = f * LaurentPolynomial.T (L : ℤ))
    (z : ℂˣ) :
    P.eval (z : ℂ) = (z : ℂ)^L * stage16_laurentEval z f := by
  have h := congrArg (stage16_laurentEval z) hP
  simpa only [stage16_laurentEval_toLaurent, map_mul, stage16_laurentEval_T_nat,
    mul_comm] using h

/-- Simultaneous polynomial clearing is an existence theorem, not an input
hypothesis, and the resulting coefficient functions are actually entire. -/
theorem stage16_laurentMatrix_exists_entire_clearing
    {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n (LaurentPolynomial ℂ)) :
    ∃ L : ℕ, 1 ≤ L ∧ ∃ P : Matrix m n (Polynomial ℂ),
      (∀ i j, Polynomial.toLaurent (P i j) = A i j * LaurentPolynomial.T (L : ℤ)) ∧
      ∀ z : ℂˣ, ∀ i j,
        (polynomialEntireAlgHom (P i j)).val (z : ℂ) =
          (z : ℂ)^L * stage16_laurentEval z (A i j) := by
  obtain ⟨L, hL, P, hP⟩ := stage16_laurentMatrix_exists_positive_clearing A
  exact ⟨L, hL, P, hP, fun z i j => stage16_laurent_clearing_eval _ _ _ (hP i j) z⟩

end StrictEUnit
