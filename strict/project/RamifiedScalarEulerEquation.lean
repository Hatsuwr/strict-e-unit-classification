import RamifiedTwistedJet
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem ramification_logCoefficientMap (N : ℕ) (hN : N ≠ 0) (b : LaurentSeries K) :
    stage38_logRamification N hN (Polynomial.C b) = stage61_logCoefficientMap N hN b := by
  change Polynomial.map (stage38_laurentRamification N hN).toRingHom (Polynomial.C b) = _
  rw [Polynomial.map_C]
  rfl

theorem ramified_external_power_scalarEuler (N : ℕ) (hN : N ≠ 0)
    (m : ℤ) (rho : K) (hm : (m : K) / (N : K) = rho)
    (n : ℕ) (b : Polynomial (PowerSeries K)) (p : Polynomial (LaurentSeries K)) :
    stage61_logLeftEulerAction N hN n b
      (Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN p) =
      Polynomial.C (HahnSeries.single m (1 : K)) * stage38_logRamification N hN
        (∑ i : Fin (n+1), Polynomial.C (HahnSeries.ofPowerSeries ℤ K (b.coeff i.val)) *
          (twistedLogPolynomialEuler rho)^[i.val] p) := by
  classical
  simp only [stage61_logLeftEulerAction, ramified_external_power_twistedEuler_iterate N hN m rho hm,
    map_sum, map_mul, ramification_logCoefficientMap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem actualFourier_ramified_lift_equation {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : K) / (N : K) = frobeniusRootSeedExponent _ i) :
    stage61_logLeftEulerAction N hN nu (stage61_fourierLift A hf)
      (Polynomial.C (HahnSeries.single m (1 : K)) *
        stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i)) = 0 := by
  rw [ramified_external_power_scalarEuler N hN m _ hm]
  have he := sameFourierTwistedAmplitude_equation A hf hc i
  change (∑ k : Fin (nu+1), Polynomial.C (HahnSeries.ofPowerSeries ℤ K
    ((stage61_fourierLift A hf).coeff k.val)) *
    (twistedLogPolynomialEuler (frobeniusRootSeedExponent _ i))^[k.val]
      (sameFourierTwistedAmplitude A hf i)) = 0 at he
  rw [he, map_zero, mul_zero]

theorem actualFourier_ramified_ordinary_equation {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (i : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0))
    (N : ℕ) (hN : N ≠ 0) (m : ℤ)
    (hm : (m : K) / (N : K) = frobeniusRootSeedExponent _ i) :
    (∑ l : Fin (nu+1), Polynomial.aeval (stage38_sourceCoordinate (K := K) N)
      (stage53_fourierCoeff A l) * (stage38_sourceOrdinary N)^[l.val]
        (Polynomial.C (HahnSeries.single m (1 : K)) *
          stage38_logRamification N hN (sameFourierTwistedAmplitude A hf i))) = 0 := by
  apply (stage61_logMonic_same_normalOrder_annihilation N hN A hf hc _).mp
  rw [stage61_fourierMonic, stage61_logLeftEulerAction_C_mul,
    actualFourier_ramified_lift_equation A hf hc i N hN m hm, mul_zero]
end StrictEUnit
end
