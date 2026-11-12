import AllClassFinitePrefixFilter

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Integer translation of all exponents preserves their common binomial
prefix denominator. The integer shift may be negative. -/
theorem jointBinomialPrefixDenominators_integer_shift {ι : Type*}
    (rho : ι → K) (h : JointBinomialPrefixDenominators rho) (L : ℤ) :
    JointBinomialPrefixDenominators (fun i =>rho i+(L : K)) := by
  obtain ⟨C,hC,hden⟩ := h
  refine ⟨C,hC,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm i
  rw [← field_choose_eq_descPochhammer_div,Ring.add_choose_eq _ (Commute.all _ _),Finset.mul_sum]
  apply IsIntegral.sum
  rintro ⟨a,b⟩ hab
  have hab' := Finset.mem_antidiagonal.mp hab
  have ha : IsIntegral ℤ ((D : K)*Ring.choose (rho i) a) := by
    simpa only [field_choose_eq_descPochhammer_div] using hDi a (by omega) i
  convert ha.mul (resonance_integer_choose_integral (K:=K) L b) using 1 <;> ring

/-- The full all-class, log-repeated filter has only linear degree growth. -/
theorem allClassPrefixFilter_natDegree_le {q : ℕ} (rho : Fin q → K)
    (L : ℤ) (N d : ℕ) :
    (allClassPrefixFilter rho L N d).natDegree≤(q*(d+1))*N := by
  rw [allClassPrefixFilter,Polynomial.natDegree_pow]
  have h := fallingCompositeSymbol_natDegree_le (fun i =>rho i+(L : K)) id (fun _ =>N) N (fun _ =>le_rfl)
  calc
    _ ≤ (d+1)*(q*N) := Nat.mul_le_mul_left (d+1) h
    _ = (q*(d+1))*N := by ring

/-- The very filter proved to annihilate every class prefix also has common
exponential connection-coefficient denominators. No filtered-solution
arithmetic is assumed here. -/
theorem allClassPrefixFilter_connection_denominators {r q : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ M : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(M+1) ∧
      ∀ m,m≤M →∀ l,l≤M →∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : Fin q → K) (hrho : JointBinomialPrefixDenominators rho) (L : ℤ) (d : ℕ) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
        (powerSeriesEulerPolynomialConnection C (allClassPrefixFilter rho L N d) i j)) := by
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
  · intro l hl i j
    have hbound : R*N≤(R+1)*N := Nat.mul_le_mul_right N (Nat.le_succ R)
    have hl' : l≤(R+1)*N := hl.trans (by nlinarith)
    have hv : ∀ k : ℕ,IsIntegral ℤ ((e : K)^R*(allClassPrefixFilter rho L N d).eval (k : K)) := by
      intro k
      have h := (fallingCompositeSymbol_eval_integral (fun i =>rho i+(L : K)) id (fun _ =>N)
        N (fun _ =>le_rfl) (e : K)
        (by intro m hm v;rw [field_choose_eq_descPochhammer_div];exact hei m hm v) k).pow (d+1)
      simpa only [mul_pow,← pow_mul,allClassPrefixFilter,Polynomial.eval_pow,R] using h
    have h := powerSeriesEulerPolynomialConnection_integral C (allClassPrefixFilter rho L N d)
      (R*N) l (allClassPrefixFilter_natDegree_le rho L N d) (D : K) ((e : K)^R)
      (fun m hm i j =>hDi m (hm.trans hbound) l hl' i j) (fun k _ =>hv k) i j
    simpa only [Nat.cast_mul,Nat.cast_pow] using h

end StrictEUnit
end
