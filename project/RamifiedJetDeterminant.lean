import RamifiedTwistedJet
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem ramified_external_power_jet_det_ne_zero {n : ℕ}
    (N : ℕ) (hN : N ≠ 0) (m : Fin n → ℤ) (rho : Fin n → K)
    (hm : ∀ j, (m j : K) / (N : K) = rho j)
    (p : Fin n → Polynomial (LaurentSeries K))
    (hp : (Matrix.of (fun i j : Fin n =>
      (twistedLogPolynomialEuler (rho j))^[i.val] (p j))).det ≠ 0) :
    (Matrix.of (fun i j : Fin n => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j)))).det ≠ 0 := by
  let Y := Matrix.of (fun i j : Fin n =>
    (twistedLogPolynomialEuler (rho j))^[i.val] (p j))
  have hmat : Matrix.of (fun i j : Fin n => (stage38_sourceEuler N)^[i.val]
      (Polynomial.C (HahnSeries.single (m j) (1 : K)) *
        stage38_logRamification N hN (p j))) =
    Y.map (stage38_logRamification N hN) *
      Matrix.diagonal (fun j => Polynomial.C (HahnSeries.single (m j) (1 : K))) := by
    apply Matrix.ext
    intro i j
    simpa only [Matrix.of_apply, Matrix.mul_diagonal, Matrix.map_apply, Y, mul_comm] using
      ramified_external_power_twistedEuler_iterate N hN (m j) (rho j) (hm j) (p j) i.val
  rw [hmat, Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero
  · change ((stage38_logRamification N hN).toRingHom.mapMatrix Y).det ≠ 0
    rw [← RingHom.map_det (stage38_logRamification N hN).toRingHom]
    intro h
    apply hp
    exact stage38_logRamification_injective N hN (h.trans (map_zero _).symm)
  · apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply Polynomial.C_ne_zero.mpr
    intro h
    have hh := congrArg (fun x : LaurentSeries K => x.coeff (m j)) h
    simpa using hh
end StrictEUnit
end
