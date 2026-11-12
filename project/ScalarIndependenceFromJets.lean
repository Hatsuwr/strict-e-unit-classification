import ActualFourierRamifiedJet
noncomputable section
attribute [-instance] Polynomial.module
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

theorem scalar_linearIndependent_of_jet_det
    {K R : Type*} [Field K] [CommRing R] [IsDomain R] [Algebra K R]
    {n : ℕ} (d : R →ₗ[K] R) (y : Fin n → R)
    (hy : (Matrix.of (fun i j : Fin n => d^[i.val] (y j))).det ≠ 0) :
    LinearIndependent K y := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  have hz : (Matrix.of (fun i j : Fin n => d^[i.val] (y j))).mulVec
      (fun j => algebraMap K R (c j)) = 0 := by
    funext i
    have h := congrArg (fun x => (d ^ i.val) x) hc
    simp only [map_sum, map_smul, map_zero, Module.End.pow_apply] at h
    simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Algebra.smul_def,
      mul_comm, Pi.zero_apply] using h
  have hj := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hy hz) j
  exact (algebraMap K R).injective (hj.trans (map_zero _).symm)

theorem actualFourier_ramified_scalar_independent {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K] {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → K) (hf : Stage56FiniteFuchs A)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → K) (p : Fin nu → Polynomial (LaurentSeries K))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (N : ℕ) (hN : N ≠ 0) (m : Fin nu → ℤ)
    (hm : ∀ j, (m j : K) / (N : K) = rho j) :
    LinearIndependent K (fun j => Polynomial.C (HahnSeries.single (m j) (1 : K)) *
      stage38_logRamification N hN (p j)) := by
  let d := (stage61_logEulerDerivation (K := K) N).toLinearMap
  have hd : (d : Polynomial (LaurentSeries K) → Polynomial (LaurentSeries K)) =
      stage38_sourceEuler N := rfl
  apply scalar_linearIndependent_of_jet_det d
  simp only [hd]
  exact actualFourier_ramified_jet_det_ne_zero A hf e rho p hrho hp N hN m hm
end StrictEUnit
end
