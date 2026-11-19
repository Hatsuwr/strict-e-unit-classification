import FiniteLogMatrixExponential

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K I : Type*} [Field K] [CharZero K] [Fintype I] [DecidableEq I]

/-- The constructed finite exponential solves its literal constant matrix
logarithmic equation; this is not supplied as a base-unit hypothesis. -/
theorem finiteLogMatrixExponential_equation (N : Matrix I I K) (hN : IsNilpotent N) :
    (fun i j =>(finiteLogMatrixExponential N i j).derivative)=
      N.map Polynomial.C * finiteLogMatrixExponential N := by
  funext i j
  apply Polynomial.ext
  intro d
  simp only [Polynomial.coeff_derivative,finiteLogMatrixExponential_coeff N hN,
    Matrix.mul_apply,Matrix.map_apply,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul]
  have hf : (((d+1).factorial:K)⁻¹)*((d+1:ℕ):K)=(d.factorial:K)⁻¹ := by
    rw [Nat.factorial_succ,Nat.cast_mul]
    have hd : ((d+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
    have hdf : (d.factorial:K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
    push_cast at hd ⊢
    field_simp [hd,hdf]
  simp only [Nat.cast_add,Nat.cast_one] at hf
  calc
    ((↑(d+1).factorial)⁻¹*(N^(d+1)) i j)*((d:K)+1) =
        (d.factorial:K)⁻¹*(N^(d+1)) i j := by
      calc
        _ = (((↑(d+1).factorial:K)⁻¹)*((d:K)+1))*(N^(d+1)) i j := by ring
        _ = _ := by rw [hf]
    _ = ∑ k,N i k*((d.factorial:K)⁻¹*(N^d) k j) := by
      rw [pow_succ',Matrix.mul_apply,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
end StrictEUnit
end
