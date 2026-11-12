import MatrixDualBinomial

/-! Coordinate and scalar normalization of the literal accepted matrix dual
identity. The derivative remains linear only over its constant field. -/

noncomputable section

open scoped BigOperators Matrix

namespace StrictEUnit

/-- Powers of the actual column derivative agree with scalar function iterates
at every coordinate. -/
theorem matrixColumnDerivative_pow_apply
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (d : Derivation k F F) (r n : ℕ) (v : Fin r → F) (i : Fin r) :
    (((matrixColumnDerivative d r)^n) v) i = (d^[n]) (v i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      change d ((((matrixColumnDerivative d r)^n) v) i) = (d^[n + 1]) (v i)
      rw [ih, Function.iterate_succ_apply']

/-- The shifted dual identity, at one coordinate, with all constant-field
scalars transported to the target field and ordinary factorial division. -/
theorem matrix_connection_divided_shifted_entry
    {k F : Type*} [Field k] [CharZero k] [Field F] [CharZero F] [Algebra k F]
    (d : Derivation k F F) {r : ℕ} (A : Matrix (Fin r) (Fin r) F)
    (n j : ℕ) (P : Fin r → F) (i : Fin r) :
    (∑ l : Fin r, matrixConnectionSequence d A n i l *
      dualDividedColumn (matrixDualColumn d A) P j l) / (n.factorial : F) =
      ∑ h ∈ Finset.range (n + 1),
        ((-1 : F)^h * ((j + h).choose h : F)) *
          (d^[n - h]) (dualDividedColumn (matrixDualColumn d A) P (j + h) i) /
            ((n - h).factorial : F) := by
  have hraw :
      (n.factorial : F)⁻¹ * (∑ l : Fin r, matrixConnectionSequence d A n i l *
        dualDividedColumn (matrixDualColumn d A) P j l) =
      ∑ h ∈ Finset.range (n + 1),
        (((-1 : F)^h * ((j + h).choose h : F)) / ((n - h).factorial : F)) *
          (d^[n - h]) (dualDividedColumn (matrixDualColumn d A) P (j + h) i) := by
    have hi := congrFun (matrix_connection_divided_shifted d A n j P) i
    simp only [Finset.sum_apply, Pi.smul_apply] at hi
    simpa only [Matrix.mulVec, dotProduct, Algebra.smul_def, map_inv₀,
      map_natCast, map_div₀, map_mul, map_pow, map_neg, map_one,
      matrixColumnDerivative_pow_apply] using hi
  calc
    _ = (n.factorial : F)⁻¹ * (∑ l : Fin r, matrixConnectionSequence d A n i l *
        dualDividedColumn (matrixDualColumn d A) P j l) := by rw [div_eq_mul_inv, mul_comm]
    _ = _ := hraw
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      ring

end StrictEUnit

end
