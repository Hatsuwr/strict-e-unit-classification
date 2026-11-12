import SelectedFourierScalarNormalForm
import Stage53FourierTupleNonzero
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem actualFourier_leading_monomial {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A) :
    stage53_fourierCoeff A (Fin.last nu) =
      Polynomial.monomial mu (stage61_fourierCorner A) := by
  classical
  rw [stage53_fourierCoeff_of_columns_above_zero A (Fin.last nu)
    (fun i j hj => by simp only [Fin.val_last] at hj; omega)]
  rw [Finset.sum_eq_single (Fin.last mu)]
  · simp only [Fin.val_last, stage61_fourierCorner]
    exact Polynomial.C_mul_X_pow_eq_monomial
  · intro i hi hne
    have him : i.val < mu := by
      have hle := Nat.le_of_lt_succ i.isLt
      have hn : i.val ≠ mu := by
        intro h
        exact hne (Fin.ext h)
      omega
    rw [stage56_fuchs_topColumn A hf i him, mul_zero, Polynomial.C_0, zero_mul]
  · intro h
    exact (h (Finset.mem_univ _)).elim
end StrictEUnit
end
