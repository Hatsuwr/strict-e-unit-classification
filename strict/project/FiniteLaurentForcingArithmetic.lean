import LaurentForcingShiftArithmetic

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def zeroPaddedForcingColumn {r : ℕ} (b : Fin r →LaurentSeries K) :
    (s : ℕ) →Fin (r+s) →LaurentSeries K
  | 0 => b
  | s+1 => Fin.cases 0 (zeroPaddedForcingColumn b s)

theorem zeroPaddedForcingColumn_arithmetic {r : ℕ}
    (b : Fin r →LaurentSeries K) (hb : LaurentForcingArithmetic b) (s : ℕ) :
    LaurentForcingArithmetic (zeroPaddedForcingColumn b s) := by
  induction s with
  | zero =>exact hb
  | succ s ih =>
    obtain ⟨W,C,hC,hlow,hden⟩ := ih
    refine ⟨W,C,hC,?_,?_⟩
    · intro i l hl
      cases i using Fin.cases with
      | zero =>rfl
      | succ i =>exact hlow i l hl
    · intro N
      obtain ⟨D,hD,hDb,hDi⟩ := hden N
      refine ⟨D,hD,hDb,?_⟩
      intro i l hl
      cases i using Fin.cases with
      | zero =>simp only [zeroPaddedForcingColumn,Fin.cases_zero,HahnSeries.coeff_zero,mul_zero];exact isIntegral_zero
      | succ i =>exact hDi i l hl

/-- Adjoin one constant coefficient for each specified integer forcing mode.
Only the original source coordinates receive the new forcing columns. -/
def finiteLaurentForcingConnection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r →LaurentSeries K)
    (k : ℕ →ℤ) : (s : ℕ) →Matrix (Fin (r+s)) (Fin (r+s)) (LaurentSeries K)
  | 0 =>A
  | s+1 =>constantForcingConnection (finiteLaurentForcingConnection A b k s)
      (fun i =>HahnSeries.single (k s) (1:K)*zeroPaddedForcingColumn b s i)

/-- Every fixed finite Laurent forcing family preserves the genuine divided
connection arithmetic, including arbitrary negative integer exponents. -/
theorem finiteLaurentForcingConnection_arithmetic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r →LaurentSeries K)
    (hA : LaurentDividedConnectionArithmetic A) (hb : LaurentForcingArithmetic b)
    (k : ℕ →ℤ) (s : ℕ) :
    LaurentDividedConnectionArithmetic (finiteLaurentForcingConnection A b k s) := by
  induction s with
  | zero =>exact hA
  | succ s ih =>
    exact constantForcingConnection_arithmetic _ _ ih
      (laurentForcingArithmetic_integer_shift _ (zeroPaddedForcingColumn_arithmetic b hb s) (k s))

end StrictEUnit
end
