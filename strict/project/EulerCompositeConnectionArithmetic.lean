import FallingCompositeSymbols

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Evaluate the genuine connection endomorphism, then read its unit-row matrix.
Products of symbols therefore mean COMPOSITIONS, not pointwise matrix products. -/
def powerSeriesEulerPolynomialConnection {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (P : Polynomial K) :
    Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
  (Polynomial.aeval (powerSeriesEulerRowConnection C) P
    (fun l => (1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i l)) j

theorem powerSeriesEulerPolynomialConnection_newton {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (P : Polynomial K)
    (R : ℕ) (hP : P.natDegree≤R) (i j : Fin r) :
    powerSeriesEulerPolynomialConnection C P i j=
      ∑ k ∈ Finset.range (R+1),PowerSeries.C K (fallingNewtonCoefficient P k)*
        powerSeriesEulerDividedConnection C k i j := by
  have he := fallingNewtonSum_eq P R hP
  unfold powerSeriesEulerPolynomialConnection
  conv_lhs => rw [← he]
  simp only [fallingNewtonSum,map_sum,map_mul,Polynomial.aeval_C,
    LinearMap.sum_apply,Module.End.mul_apply,Module.algebraMap_end_apply,
    powerSeriesEulerRowConnection_divided,Finset.sum_apply,Pi.smul_apply,
    PowerSeries.smul_eq_C_mul]

/-- A common source-connection denominator and a common value denominator
suffice for the exact polynomial operator. No determinant or factorial appears. -/
theorem powerSeriesEulerPolynomialConnection_integral {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (P : Polynomial K)
    (R l : ℕ) (hP : P.natDegree≤R) (D e : K)
    (hC : ∀ m,m≤R → ∀ i j,IsIntegral ℤ
      (D*PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (hval : ∀ k,k≤R → IsIntegral ℤ (e*P.eval (k : K))) (i j : Fin r) :
    IsIntegral ℤ (D*e*PowerSeries.coeff K l (powerSeriesEulerPolynomialConnection C P i j)) := by
  rw [powerSeriesEulerPolynomialConnection_newton C P R hP i j]
  simp only [map_sum,PowerSeries.coeff_C_mul,Finset.mul_sum]
  apply IsIntegral.sum
  intro k hk
  have hkR : k≤R := by have := Finset.mem_range.mp hk;omega
  have h := (fallingNewtonCoefficient_integral P e R hval k hkR).mul (hC k hkR i j)
  convert h using 1 <;> ring

/-- Fixed-length composites of ALL selected shifted filters retain exponential
prefix bounds. The same denominator works for every choice of factors and orders. -/
theorem powerSeriesEulerCompositeConnection_denominators {r : ℕ} {ι : Type*}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ (u : Fin q → ι) (ms : Fin q → ℕ),(∀ i,ms i≤N) →
        ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
          (powerSeriesEulerPolynomialConnection C (fallingCompositeSymbol rho u ms) i j)) := by
  obtain ⟨H,hH,hneg⟩ := jointBinomialPrefixDenominators_neg rho hrho
  refine ⟨B^(q+1)*H^q,one_le_mul_of_one_le_of_one_le (one_le_pow₀ hB) (one_le_pow₀ hH),?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden ((q+1)*N)
  obtain ⟨e,he,heb,hei⟩ := hneg N
  refine ⟨D*e^q,Nat.mul_pos hD (pow_pos he q),?_,?_⟩
  · rw [Nat.cast_mul,Nat.cast_pow,mul_pow,← pow_mul,← pow_mul]
    apply mul_le_mul ?_ ?_ (pow_nonneg (Nat.cast_nonneg e) _) (pow_nonneg (le_trans zero_le_one hB) _)
    · exact hDb.trans (pow_le_pow_right₀ hB (by nlinarith))
    · calc
        (e : ℝ)^q ≤ (H^(N+1))^q := pow_le_pow_left₀ (Nat.cast_nonneg e) heb q
        _ = H^(q*(N+1)) := by rw [← pow_mul];congr 1;exact Nat.mul_comm _ _
  · intro u ms hm l hl i j
    have hbound : q*N≤(q+1)*N := Nat.mul_le_mul_right N (Nat.le_succ q)
    have hl' : l≤(q+1)*N := hl.trans (by nlinarith)
    have h := powerSeriesEulerPolynomialConnection_integral C (fallingCompositeSymbol rho u ms)
      (q*N) l (fallingCompositeSymbol_natDegree_le rho u ms N hm) (D : K) ((e : K)^q)
      (fun m hm i j => hDi m (hm.trans hbound) l hl' i j)
      (fun k _ => fallingCompositeSymbol_eval_integral rho u ms N hm (e : K)
        (by intro m hm v;rw [field_choose_eq_descPochhammer_div];exact hei m hm v) k) i j
    simpa only [Nat.cast_mul,Nat.cast_pow] using h

end StrictEUnit
end
