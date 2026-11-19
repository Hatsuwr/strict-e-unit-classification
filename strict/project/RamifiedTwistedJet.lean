import ActualFourierRamifiedBlock
import LogSolutionConnectionIntertwining
noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem ramified_external_power_twistedEuler (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (p : Polynomial (LaurentSeries K)) :
    stage38_sourceEuler N (Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN p) =
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN (twistedLogPolynomialEuler rho p) := by
  have hd : stage38_sourceEuler N (stage38_logRamification N hN p) =
      stage38_logRamification N hN (logPolynomialEuler 1 p) := by
    simpa [stage38_sourceEuler_apply] using
      stage38_logRamification_sourceEuler N hN 1 p
  rw [stage38_sourceEuler_mul, hd, stage61_logEuler_monomial, hm, mul_one,
    twistedLogPolynomialEuler_ring_formula, map_add, map_mul]
  change _ = Polynomial.C (HahnSeries.single m (1 : K)) *
    (stage38_logRamification N hN (logPolynomialEuler 1 p) +
      stage38_logRamification N hN (Polynomial.C (HahnSeries.single 0 rho)) *
        stage38_logRamification N hN p)
  rw [stage38_logRamification_constant]
  have hs : Polynomial.C (HahnSeries.single m rho) =
      Polynomial.C (HahnSeries.single m (1 : K)) *
        Polynomial.C (HahnSeries.single 0 rho) := by
    rw [← Polynomial.C_mul, HahnSeries.single_mul_single, add_zero, one_mul]
  rw [hs]
  ring

theorem ramified_external_power_twistedEuler_iterate (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (p : Polynomial (LaurentSeries K)) (i : ℕ) :
    (stage38_sourceEuler N)^[i] (Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN p) =
    Polynomial.C (HahnSeries.single m (1 : K)) *
      stage38_logRamification N hN ((twistedLogPolynomialEuler rho)^[i] p) := by
  induction i with
  | zero => rfl
  | succ i hi =>
    rw [Function.iterate_succ_apply', hi, ramified_external_power_twistedEuler N hN m rho hm,
      Function.iterate_succ_apply']
end StrictEUnit
end
