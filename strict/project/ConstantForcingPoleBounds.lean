import ConstantForcingDividedFormula

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem constantForcingColumn_linear_poles {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K) (P W : ℕ)
    (hA : ∀ a i j l,l< -((P*a : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l=0)
    (hb : ∀ j l,l< -(W : ℤ) →(b j).coeff l=0) :
    ∀ m i l,l< -(((P+W+1)*m : ℕ) : ℤ) →
      (constantForcingColumn (stage14_laurentAlgebraDerivation (k:=K)) A b m i/
        (m.factorial : LaurentSeries K)).coeff l=0 := by
  intro m i l hl
  rw [constantForcingColumn_divided_coeff]
  apply Finset.sum_eq_zero
  intro a ha
  have ham : a<m := Finset.mem_range.mp ha
  have hbound : P*a+W+(m-1-a)≤(P+W+1)*m := by
    have hpa := Nat.mul_le_mul_left P (show a≤m by omega)
    have hwm := Nat.mul_le_mul_left W (show 1≤m by omega)
    have hh : m-1-a≤m := by omega
    nlinarith
  have hbound' : ((P*a : ℕ) : ℤ)+(W : ℤ)+((m-1-a : ℕ) : ℤ)≤(((P+W+1)*m : ℕ) : ℤ) := by
    exact_mod_cast hbound
  rw [LaurentSeries.hasseDeriv_coeff,HahnSeries.coeff_sum]
  have hs : (∑ j,((matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
      (a.factorial : LaurentSeries K))*b j).coeff (l+((m-1-a : ℕ) : ℤ)))=0 := by
    apply Finset.sum_eq_zero
    intro j hj
    exact forcing_laurent_product_lower _ (b j) (-((P*a : ℕ) : ℤ)) (-(W : ℤ))
      (hA a i j) (hb j) _ (by omega)
  rw [hs,smul_zero,mul_zero]

theorem constantForcingConnection_linear_poles {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K) (P W : ℕ)
    (hA : ∀ a i j l,l< -((P*a : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A a i j/
        (a.factorial : LaurentSeries K)).coeff l=0)
    (hb : ∀ j l,l< -(W : ℤ) →(b j).coeff l=0) :
    ∀ m i j l,l< -(((P+W+1)*m : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K))
        (constantForcingConnection A b) m i j/(m.factorial : LaurentSeries K)).coeff l=0 := by
  intro m i j l hl
  obtain ⟨htop,hmain,hcol⟩ := constantForcingConnection_sequence
    (stage14_laurentAlgebraDerivation (k:=K)) A b m
  cases i using Fin.cases with
  | zero =>
    rw [htop]
    split_ifs with h
    · rcases h with ⟨rfl,rfl⟩
      simp only [Nat.mul_zero,Nat.cast_zero,neg_zero] at hl
      simp only [Nat.factorial_zero,Nat.cast_one,div_one,HahnSeries.coeff_one,if_neg (by omega : l≠0)]
    · simp
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [hcol]
      exact constantForcingColumn_linear_poles A b P W hA hb m i l hl
    | succ j =>
      rw [hmain]
      apply hA m i j l
      have hp : P*m≤(P+W+1)*m := Nat.mul_le_mul_right m (by omega)
      have hp' : ((P*m : ℕ) : ℤ)≤(((P+W+1)*m : ℕ) : ℤ) := by exact_mod_cast hp
      omega

end StrictEUnit
end
