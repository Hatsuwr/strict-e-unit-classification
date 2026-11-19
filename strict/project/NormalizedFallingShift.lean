import BinomialPrefixShiftClosure

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def normalizedFallingSymbol (m : ℕ) : Polynomial K :=
  Polynomial.C ((m.factorial : K)⁻¹)*descPochhammer K m

theorem normalizedFallingSymbol_eval (m : ℕ) (x : K) :
    (normalizedFallingSymbol (K:=K) m).eval x=Ring.choose x m := by
  rw [field_choose_eq_descPochhammer_div]
  simp only [normalizedFallingSymbol,Polynomial.eval_mul,Polynomial.eval_C,div_eq_mul_inv,mul_comm]

/-- Polynomial Chu-Vandermonde identity with the exact factorial normalization. -/
theorem normalizedFallingSymbol_translate (alpha : K) (m : ℕ) :
    (normalizedFallingSymbol (K:=K) m).comp (Polynomial.X+Polynomial.C alpha)=
      ∑ ab ∈ Finset.antidiagonal m,
        Polynomial.C (Ring.choose alpha ab.1)*normalizedFallingSymbol (K:=K) ab.2 := by
  apply Polynomial.funext
  intro x
  simp only [Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
    Polynomial.eval_finset_sum,Polynomial.eval_mul,normalizedFallingSymbol_eval]
  rw [add_comm,Ring.add_choose_eq _ (Commute.all _ _)]

/-- The identity applies to genuine K-linear endomorphisms, with no false
linearity over a ring of differentiated functions. -/
theorem normalizedFallingSymbol_aeval_translate {R : Type*} [Ring R] [Algebra K R]
    (L : R) (alpha : K) (m : ℕ) :
    Polynomial.aeval (L+algebraMap K R alpha) (normalizedFallingSymbol (K:=K) m)=
      ∑ ab ∈ Finset.antidiagonal m,
        (Ring.choose alpha ab.1) • Polynomial.aeval L (normalizedFallingSymbol (K:=K) ab.2) := by
  have h := congrArg (Polynomial.aeval L) (normalizedFallingSymbol_translate alpha m)
  simpa only [Polynomial.aeval_comp,map_add,Polynomial.aeval_X,Polynomial.aeval_C,
    map_sum,map_mul,Algebra.smul_def] using h

end StrictEUnit
end
