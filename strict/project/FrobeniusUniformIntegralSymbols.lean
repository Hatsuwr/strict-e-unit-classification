import FrobeniusIndicialDenominatorPower
import Mathlib.RingTheory.Algebraic.Integral

/-! ONE positive integer clears all translated Fourier symbols, at every
natural shift. The scalar indicial values are retained exactly. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem finite_algebraic_polynomials_positive_clearing [Algebra.IsAlgebraic ℤ K]
    {ι : Type*} [Fintype ι] (P : ι → Polynomial K) :
    ∃ b : ℕ,0<b ∧ ∀ i j,IsIntegral ℤ ((b : K)*(P i).coeff j) := by
  let s : Finset K := Finset.univ.biUnion (fun i => (P i).coeffs)
  obtain ⟨z,hz,hi⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ s
  have hcoeff (i : ι) (j : ℕ) : IsIntegral ℤ ((z : K)*(P i).coeff j) := by
    by_cases hj : (P i).coeff j=0
    · simpa only [hj,mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : K))
    · have hmem : (P i).coeff j∈s := Finset.mem_biUnion.mpr
        ⟨i,Finset.mem_univ i,Polynomial.coeff_mem_coeffs _ _ hj⟩
      simpa only [Algebra.smul_def] using hi _ hmem
  have he : ((z.natAbs^2 : ℕ) : K) = (z : K)^2 := by
    have h : ((z.natAbs^2 : ℕ) : ℤ)=z^2 := by rw [Nat.cast_pow,Int.natCast_natAbs,sq_abs]
    have hc := congrArg (fun t : ℤ => (t : K)) h
    simpa only [Int.cast_natCast,Int.cast_pow] using hc
  refine ⟨z.natAbs^2,pow_pos (Int.natAbs_pos.mpr hz) _,?_⟩
  intro i j
  rw [he,pow_two,mul_assoc]
  exact (isIntegral_algebraMap (R := ℤ) (A := K) (x := z)).mul (hcoeff i j)

theorem polynomial_doubleTranslate (P : Polynomial K) (rho c : K) :
    (P.comp (Polynomial.X+Polynomial.C rho)).comp (Polynomial.X+Polynomial.C c) =
      P.comp (Polynomial.X+Polynomial.C (rho+c)) := by
  rw [Polynomial.comp_assoc]
  congr 1
  simp only [Polynomial.add_comp,Polynomial.X_comp,Polynomial.C_comp,Polynomial.C_add]
  abel

theorem polynomial_integral_clearing_natTranslate (P : Polynomial K) (rho : K)
    (b : ℕ) (h : ∀ j,IsIntegral ℤ ((b : K)*(P.comp (Polynomial.X+Polynomial.C rho)).coeff j))
    (n : ℕ) :
    ∀ j,IsIntegral ℤ ((b : K)*(P.comp (Polynomial.X+Polynomial.C (rho+(n : K)))).coeff j) := by
  let Q := Polynomial.C (b : K)*(P.comp (Polynomial.X+Polynomial.C rho))
  have hQ : ∀ j,Q.coeff j ∈ (integralClosure ℤ K).toSubring := by
    intro j
    simpa only [Q,Polynomial.coeff_C_mul] using h j
  have ht := polynomial_subring_natTranslate (integralClosure ℤ K).toSubring Q hQ n
  have he : Q.comp (Polynomial.X+Polynomial.C (n : K)) =
      Polynomial.C (b : K)*(P.comp (Polynomial.X+Polynomial.C (rho+(n : K)))) := by
    dsimp only [Q]
    rw [Polynomial.mul_comp,Polynomial.C_comp,polynomial_doubleTranslate]
  rw [he] at ht
  simpa only [Polynomial.coeff_C_mul] using ht

/-- One scalar works simultaneously for a finite exponent family, all Fourier
coefficient symbols, every natural translate and every logarithmic coefficient. -/
theorem finite_fourier_uniform_integral_symbols [Algebra.IsAlgebraic ℤ K]
    {ι : Type*} [Fintype ι] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (hf : Stage56FiniteFuchs A) (rho : ι → K) :
    ∃ b : ℕ,0<b ∧ ∀ (i : ι) (k n j : ℕ),IsIntegral ℤ
      ((b : K)*((sameFourierEulerCoefficientSymbols A hf k).comp
        (Polynomial.X+Polynomial.C (rho i+(n : K)))).coeff j) := by
  let P : (ι × Fin (ν+1)) → Polynomial K := fun ik =>
    (sameFourierEulerCoefficientSymbols A hf ik.2.val).comp (Polynomial.X+Polynomial.C (rho ik.1))
  obtain ⟨b,hb,hclear⟩ := finite_algebraic_polynomials_positive_clearing P
  refine ⟨b,hb,?_⟩
  intro i k n j
  by_cases hk : k≤ν
  · exact polynomial_integral_clearing_natTranslate
      (sameFourierEulerCoefficientSymbols A hf k) (rho i) b
      (hclear (i,⟨k,by omega⟩)) n j
  · rw [sameFourierEulerCoefficientSymbols_eq_zero_above_order A hf k (Nat.lt_of_not_ge hk)]
    simpa only [Polynomial.zero_comp,Polynomial.coeff_zero,mul_zero] using
      (isIntegral_zero : IsIntegral ℤ (0 : K))

theorem polynomial_eventually_shifted_nat_nonzero (P : Polynomial K) (hP : P≠0) (rho : K) :
    ∃ N : ℕ,∀ n : ℕ,N≤n → P.eval (rho+(n : K))≠0 := by
  have hinj : Function.Injective (fun n : ℕ => rho+(n : K)) := by
    intro n m h
    exact Nat.cast_injective (add_left_cancel h)
  have hfinite : Set.Finite {n : ℕ | P.eval (rho+(n : K))=0} :=
    (Polynomial.finite_setOf_isRoot hP).preimage hinj.injOn
  obtain ⟨N,hN⟩ := hfinite.bddAbove
  refine ⟨N+1,?_⟩
  intro n hn hz
  have := hN hz
  omega

end StrictEUnit
end
