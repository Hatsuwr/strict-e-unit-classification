import ActualMinimalPolynomialConnection
import OrdinaryDerivativePrefix

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Reflect the SAME cleared Laurent system to ordinary power series. -/
theorem powerSeries_cleared_equation_of_laurent_system
    {K : Type*} [Field K] {r : ℕ} (f : Fin r → PowerSeries K)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T*A i j)
    (hsystem : ∀ i, laurentOrdinaryDerivation (HahnSeries.ofPowerSeries ℤ K (f i)) =
      ∑ j, A i j • HahnSeries.ofPowerSeries ℤ K (f j)) :
    ∀ i, (T : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ j, (U i j : PowerSeries K)*f j := by
  intro i
  apply HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (R:=K)
  rw [map_mul, map_sum, ← laurentOrdinaryDerivation_ofPowerSeries, hsystem,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul, ← Polynomial.algebraMap_hahnSeries_apply,
    ← Polynomial.algebraMap_hahnSeries_apply]
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  have h := congrArg (algebraMap (RatFunc K) (LaurentSeries K)) (hclear i j)
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply] using h.symm

/-- Both required family facts come from the original minimal companion data;
no new independence or PowerSeries-system premise is supplied. -/
theorem minimal_companion_powerSeries_clearing
    {K : Type*} [Field K] (G : PowerSeries K) (r : ℕ) (c : Fin r → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData (HahnSeries.ofPowerSeries ℤ K G) r c)
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion r c i j) :
    LinearIndependent (RatFunc K)
      (fun i => HahnSeries.ofPowerSeries ℤ K (ordinaryDerivativePrefix r G i)) ∧
    (∀ i, (T : PowerSeries K)*PowerSeries.derivative K (ordinaryDerivativePrefix r G i) =
      ∑ j, (U i j : PowerSeries K)*ordinaryDerivativePrefix r G j) := by
  refine ⟨?_, ?_⟩
  · simpa only [ordinaryDerivativePrefix, laurentOrdinaryDerivation_iterate_ofPowerSeries]
      using hdata.1
  · apply powerSeries_cleared_equation_of_laurent_system _ _ T U hclear
    intro i
    simpa only [ordinaryDerivativePrefix, laurentOrdinaryDerivation_iterate_ofPowerSeries]
      using hdata.2.2.2.2 i

end StrictEUnit
end
