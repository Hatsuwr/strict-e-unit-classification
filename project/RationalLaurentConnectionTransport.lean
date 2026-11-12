import LaurentDiagonalGaugeArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Higher connections commute with the actual rational-to-Laurent differential
inclusion. This identifies whole matrices, not only a selected solution. -/
theorem rational_laurent_connection_sequence {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (m : ℕ) (i j : Fin r) :
    matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K))
      (A.map (algebraMap (RatFunc K) (LaurentSeries K))) m i j=
        algebraMap (RatFunc K) (LaurentSeries K)
          (matrixConnectionSequence stage14_rationalOrdinaryDerivation A m i j) := by
  classical
  induction m generalizing i j with
  | zero =>
    simp only [matrixConnectionSequence,Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    change stage14_laurentAlgebraDerivation
        (matrixConnectionSequence stage14_laurentAlgebraDerivation
          (A.map (algebraMap (RatFunc K) (LaurentSeries K))) m i j)+
      (∑ l,matrixConnectionSequence stage14_laurentAlgebraDerivation
        (A.map (algebraMap (RatFunc K) (LaurentSeries K))) m i l*
          algebraMap (RatFunc K) (LaurentSeries K) (A l j))=
      algebraMap (RatFunc K) (LaurentSeries K)
        (stage14_rationalOrdinaryDerivation (matrixConnectionSequence stage14_rationalOrdinaryDerivation A m i j)+
          ∑ l,matrixConnectionSequence stage14_rationalOrdinaryDerivation A m i l*A l j)
    simp only [ih,stage14_laurentAlgebraDerivation_apply,stage14_rationalLaurent_differential,
      map_add,map_sum,map_mul]

theorem rational_laurent_divided_connection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (m : ℕ) (i j : Fin r) :
    matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K))
      (A.map (algebraMap (RatFunc K) (LaurentSeries K))) m i j/
        (m.factorial : LaurentSeries K)=
      algebraMap (RatFunc K) (LaurentSeries K)
        ((m.factorial : RatFunc K)⁻¹*matrixConnectionSequence stage14_rationalOrdinaryDerivation A m i j) := by
  rw [rational_laurent_connection_sequence]
  simp only [map_mul,map_inv₀,map_natCast,div_eq_mul_inv,mul_comm]

end StrictEUnit
end
