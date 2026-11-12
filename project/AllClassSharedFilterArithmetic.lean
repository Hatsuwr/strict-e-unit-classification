import AllClassPrefixConnectionArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A SINGLE integer per cutoff simultaneously covers every filter order
and every connection coefficient in that prefix. It is not a product of
separately chosen denominators for each filter order. -/
theorem allClassPrefixFilter_shared_connection_denominators {r q : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ M : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(M+1) ∧
      ∀ m,m≤M →∀ l,l≤M →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : Fin q → K) (hrho : JointBinomialPrefixDenominators rho) (L : ℤ) (d : ℕ) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
        (powerSeriesEulerPolynomialConnection C (allClassPrefixFilter rho L m d) i j)) := by
  let R := q*(d+1)
  obtain ⟨H,hH,hneg⟩ := jointBinomialPrefixDenominators_neg _
    (jointBinomialPrefixDenominators_integer_shift rho hrho L)
  refine ⟨B^(R+1)*H^R,one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ hH),?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden ((R+1)*N)
  obtain ⟨e,he,heb,hei⟩ := hneg N
  refine ⟨D*e^R,Nat.mul_pos hD (pow_pos he R),?_,?_⟩
  · rw [Nat.cast_mul,Nat.cast_pow,mul_pow,← pow_mul,← pow_mul]
    apply mul_le_mul ?_ ?_ (pow_nonneg (Nat.cast_nonneg e) _) (pow_nonneg (by linarith) _)
    · exact hDb.trans (pow_le_pow_right₀ hB (by nlinarith))
    · calc
        (e : ℝ)^R≤(H^(N+1))^R := pow_le_pow_left₀ (Nat.cast_nonneg e) heb R
        _=H^(R*(N+1)) := by rw [← pow_mul];congr 1;ring
  · intro m hm l hl i j
    have hbound : R*N≤(R+1)*N := Nat.mul_le_mul_right N (Nat.le_succ R)
    have hl' : l≤(R+1)*N := hl.trans (by nlinarith)
    have hv : ∀ k : ℕ,IsIntegral ℤ ((e : K)^R*(allClassPrefixFilter rho L m d).eval (k : K)) := by
      intro k
      have h := (fallingCompositeSymbol_eval_integral (fun i =>rho i+(L : K)) id (fun _ =>m)
        N (fun _ =>hm) (e : K)
        (by intro m hm v;rw [field_choose_eq_descPochhammer_div];exact hei m hm v) k).pow (d+1)
      simpa only [mul_pow,← pow_mul,allClassPrefixFilter,Polynomial.eval_pow,R] using h
    have h := powerSeriesEulerPolynomialConnection_integral C (allClassPrefixFilter rho L m d)
      (R*N) l ((allClassPrefixFilter_natDegree_le rho L m d).trans (Nat.mul_le_mul_left R hm)) (D : K) ((e : K)^R)
      (fun m hm i j =>hDi m (hm.trans hbound) l hl' i j) (fun k _ =>hv k) i j
    simpa only [Nat.cast_mul,Nat.cast_pow] using h


end StrictEUnit
end
