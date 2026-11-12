import MatrixDiagonalGaugeDivided
import Stage14LaurentPolynomialODEClosure
import SelectedSingularConnectionArithmetic

/-! Exact monomial gauge covariance and common arithmetic for all Laurent
coefficients. Integer binomial multipliers introduce no new denominators. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

local instance [CharZero K] : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

theorem laurentOrdinaryDerivation_eq_native :
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)=
      (LaurentSeries.derivative K : LaurentSeries K → LaurentSeries K) := by
  funext f
  ext n
  simp only [laurentOrdinaryDerivation_coeff,LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff,Ring.choose_one_right,zsmul_eq_mul,Nat.cast_one]

theorem laurentIntegerMonomial_divided_derivative [CharZero K] (w m : ℕ) :
    ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[m])
      (laurentIntegerMonomial (w : ℤ))/(m.factorial : LaurentSeries K)=
        HahnSeries.single ((w : ℤ)-(m : ℤ)) (w.choose m : K) := by
  rw [laurentOrdinaryDerivation_eq_native,LaurentSeries.derivative_iterate]
  simp only [nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))]
  simp only [laurentIntegerMonomial,LaurentSeries.hasseDeriv_single,
    Ring.choose_natCast,zsmul_eq_mul,Int.cast_natCast,mul_one]

theorem laurentIntegerMonomial_inv (w : ℤ) :
    (laurentIntegerMonomial (K:=K) w)⁻¹=laurentIntegerMonomial (-w) := by
  apply inv_eq_of_mul_eq_one_right
  simp

/-- Literal finite Leibniz sum for the full divided connection, not just a
residue or a selected row. -/
theorem laurent_diagonal_gauge_divided_connection [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (m : ℕ) (i j : Fin r) :
    matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K))
      (diagonalGaugeConnection (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A
        (fun i => laurentIntegerMonomial (w i : ℤ))) m i j/(m.factorial : LaurentSeries K)=
      ∑ ab ∈ Finset.antidiagonal m,
        HahnSeries.single ((w i : ℤ)-(ab.1 : ℤ)-(w j : ℤ)) (Nat.choose (w i) ab.1 : K)*
          (matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A ab.2 i j/
            (ab.2.factorial : LaurentSeries K)) := by
  rw [matrixConnectionSequence_divided_diagonal_gauge _ _ _
    (fun i => laurentIntegerMonomial_ne_zero _)]
  rw [show (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)=
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K) from rfl]
  simp_rw [laurentIntegerMonomial_divided_derivative]
  rw [div_eq_mul_inv,laurentIntegerMonomial_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  rw [mul_right_comm]
  congr 1
  simp only [laurentIntegerMonomial,HahnSeries.single_mul_single,mul_one,sub_eq_add_neg]

theorem laurent_diagonal_gauge_divided_coefficient [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (m : ℕ) (i j : Fin r) (l : ℤ) :
    (matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K))
      (diagonalGaugeConnection (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A
        (fun i => laurentIntegerMonomial (w i : ℤ))) m i j/
          (m.factorial : LaurentSeries K)).coeff l=
      ∑ ab ∈ Finset.antidiagonal m, (Nat.choose (w i) ab.1 : K)*
        (matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A ab.2 i j/
          (ab.2.factorial : LaurentSeries K)).coeff
            (l-(w i : ℤ)+(ab.1 : ℤ)+(w j : ℤ)) := by
  rw [laurent_diagonal_gauge_divided_connection,HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  rintro ⟨a,b⟩ hab
  conv_lhs => arg 2; rw [show l=(l-(w i : ℤ)+(a : ℤ)+(w j : ℤ))+
      ((w i : ℤ)-(a : ℤ)-(w j : ℤ)) by omega]
  rw [HahnSeries.coeff_single_mul_add]

/-- One integer clears the entire sheared divided connection prefix. The
explicit base depends only on the old base and the fixed largest weight. -/
theorem laurent_diagonal_gauge_exponential_denominators [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (w : Fin r → ℕ)
    (W : ℕ) (hw : ∀ i,w i≤W) (C : ℝ) (hC : 1≤C)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤C^(N+1) ∧
      ∀ m,m≤N → ∀ l : ℤ,l≤(N : ℤ) → ∀ i j,
        IsIntegral ℤ ((D : K)*(matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A m i j/
          (m.factorial : LaurentSeries K)).coeff l)) :
    1≤C^(W+3) ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤(C^(W+3))^(N+1) ∧
      ∀ m,m≤N → ∀ l : ℤ,l≤(N : ℤ) → ∀ i j,
        IsIntegral ℤ ((D : K)*(matrixConnectionSequence (k:=K) (stage14_laurentAlgebraDerivation (k:=K))
          (diagonalGaugeConnection (k:=K) (stage14_laurentAlgebraDerivation (k:=K)) A
            (fun i => laurentIntegerMonomial (w i : ℤ))) m i j/
              (m.factorial : LaurentSeries K)).coeff l) := by
  refine ⟨one_le_pow₀ hC,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden (2*N+W)
  refine ⟨D,hD,?_,?_⟩
  · apply hDb.trans
    rw [← pow_mul]
    apply pow_le_pow_right₀ hC
    nlinarith
  · intro m hm l hl i j
    rw [laurent_diagonal_gauge_divided_coefficient,Finset.mul_sum]
    apply IsIntegral.sum
    rintro ⟨a,b⟩ hab
    have hab' := Finset.mem_antidiagonal.mp hab
    have hb : b≤2*N+W := by omega
    have ha : (a : ℤ)≤(N : ℤ) := by exact_mod_cast (show a≤N by omega)
    have hj : (w j : ℤ)≤(W : ℤ) := by exact_mod_cast hw j
    have hwi : (0 : ℤ)≤(w i : ℤ) := Int.natCast_nonneg _
    have hl' : l-(w i : ℤ)+(a : ℤ)+(w j : ℤ)≤((2*N+W : ℕ) : ℤ) := by
      push_cast
      omega
    have hh := hDi b hb _ hl' i j
    have hc : IsIntegral ℤ (Nat.choose (w i) a : K) := ordinaryJet_natCast_integral _
    simpa only [mul_assoc,mul_left_comm,mul_comm] using hc.mul hh

end StrictEUnit
end
