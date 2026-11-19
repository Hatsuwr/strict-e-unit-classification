import TwistedFallingNormalization

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]
attribute [local instance 2000] Algebra.toModule

theorem twisted_normalized_fourier_term {μ ν : ℕ} (rho : K)
    (i : Fin (μ+1)) (j : Fin (ν+1)) (c : K) (y : Polynomial (LaurentSeries K)) :
    stage61_logZPow 1 ((ν : ℤ)-(μ : ℤ)) *
      (Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val * c)) *
        (actualTwistedLogOrdinary rho)^[j.val] (stage61_logZPow 1 (i.val : ℤ) * y)) =
      ∑ k : Fin (ν+1), stage61_logCoefficientMap 1 (by decide)
        (HahnSeries.single (stage57_exponent i j)
          (((-1 : K)^j.val * c) * (stage61_shiftedDesc i.val j.val).coeff k.val)) *
            (actualTwistedEulerEnd rho)^[k.val] y := by
  classical
  rw [actualTwistedLogOrdinary_falling]
  have hs : (descPochhammer K j.val).comp
      (Polynomial.X + Polynomial.C ((i.val : ℤ) : K)) =
      stage61_shiftedDesc (K := K) i.val j.val := by
    simp only [stage61_shiftedDesc, Int.cast_natCast]
  rw [hs,logFourier_endomorphismEval_eq_aeval,
    logFourier_endomorphism_eval_fin (K := K) (A := Polynomial (LaurentSeries K))
      (actualTwistedEulerEnd rho)
      (stage61_shiftedDesc i.val j.val)
      (ν+1) (by rw [stage61_shiftedDesc_natDegree]; exact j.isLt)]
  simp only [Finset.mul_sum, stage61_logScalar_mul]
  apply Finset.sum_congr rfl
  intro k _
  change stage61_logZPow 1 ((ν : ℤ)-(μ : ℤ)) *
      (Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val*c)) *
        (stage61_logZPow 1 ((i.val : ℤ)-(j.val : ℤ)) *
          (Polynomial.C (HahnSeries.single (0 : ℤ)
            ((stage61_shiftedDesc i.val j.val).coeff k.val)) *
              (actualTwistedEulerEnd rho)^[k.val] y))) = _
  calc
    _ = (stage61_logZPow 1 ((ν : ℤ)-(μ : ℤ)) *
        Polynomial.C (HahnSeries.single (0 : ℤ) ((-1 : K)^j.val*c)) *
        stage61_logZPow 1 ((i.val : ℤ)-(j.val : ℤ)) *
        Polynomial.C (HahnSeries.single (0 : ℤ)
          ((stage61_shiftedDesc i.val j.val).coeff k.val))) *
            (actualTwistedEulerEnd rho)^[k.val] y := by ring
    _ = _ := by
      congr 1
      simp only [stage61_logZPow, stage61_logCoefficientMap_monomial, Nat.cast_one, one_mul,
        ← Polynomial.C_mul, HahnSeries.single_mul_single,
        add_zero, one_mul, mul_one]
      congr 2
      unfold stage57_exponent
      ring


end StrictEUnit
end
