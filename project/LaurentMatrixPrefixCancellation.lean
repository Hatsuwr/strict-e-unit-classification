import AllClassPrefixConnectionArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {R : Type*} [CommRing R]

/-- Lower support convolution over an arbitrary coefficient ring, including
polynomial log coefficients. No field-of-logarithms inverse is silently used. -/
theorem laurentRing_product_prefix_zero (x y : LaurentSeries R) (a b : ℤ)
    (hx : ∀ k,k<a →x.coeff k=0) (hy : ∀ k,k<b →y.coeff k=0) :
    ∀ k,k<a+b →(x*y).coeff k=0 := by
  intro k hk
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hs := Finset.mem_addAntidiagonal.mp hij
  by_cases hi : i<a
  · rw [hx i hi,zero_mul]
  · rw [hy j (by omega),mul_zero]

theorem laurentMatrix_product_prefix_zero {r : ℕ}
    (A B : Matrix (Fin r) (Fin r) (LaurentSeries R)) (a b : ℤ)
    (hA : ∀ i j k,k<a →(A i j).coeff k=0)
    (hB : ∀ i j k,k<b →(B i j).coeff k=0) :
    ∀ i j k,k<a+b →((A*B) i j).coeff k=0 := by
  intro i j k hk
  simp only [Matrix.mul_apply,HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro l hl
  exact laurentRing_product_prefix_zero _ _ a b (hA i l) (hB l j) k hk

/-- Genuine cancellation through a supplied right inverse transfers high
vanishing to the coefficient matrix. Existence and a uniform pole bound for
that inverse are explicit obligations, not consequences of this lemma. -/
theorem laurentMatrix_prefix_cancel_right {r : ℕ}
    (F H J Z : Matrix (Fin r) (Fin r) (LaurentSeries R))
    (hF : F*H=Z) (hJ : H*J=1) (a b : ℤ)
    (hZ : ∀ i j k,k<a →(Z i j).coeff k=0)
    (hJlow : ∀ i j k,k<b →(J i j).coeff k=0) :
    ∀ i j k,k<a+b →(F i j).coeff k=0 := by
  have heq : F=Z*J := by rw [← hF,Matrix.mul_assoc,hJ,Matrix.mul_one]
  rw [heq]
  exact laurentMatrix_product_prefix_zero Z J a b hZ hJlow

end StrictEUnit
end
