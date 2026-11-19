import IndependentPolynomialRowOrder
import TypeIIDividedColumnContact
import Mathlib.RingTheory.PowerSeries.Order

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- A finite-jet bound is chosen BEFORE approximation data. A bounded nonzero
polynomial row cannot annihilate a sufficiently accurate Type-II numerator.
Zero numerators are not excluded by an extra premise. -/
theorem typeII_no_bounded_polynomial_annihilator
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (f : Fin r → PowerSeries K)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (D : ℕ) :
    ∃ Z : ℕ, 0 < Z ∧ ∀ N M : ℕ, Z ≤ M →
      ∀ Q : Polynomial K, Q ≠ 0 → Q.natDegree ≤ N →
      ∀ P : Fin r → Polynomial K,
      (∀ i, seriesContact (N+M+1) ((Q : PowerSeries K)*f i-(P i : PowerSeries K))) →
      ∀ p : Fin r → Polynomial K, (∀ i, (p i).natDegree ≤ D) → (∃ i, p i ≠ 0) →
        (∑ i, p i*P i) ≠ 0 := by
  classical
  obtain ⟨Z,hZ,horder⟩ := powerSeries_independent_bounded_polynomial_row_order f hli D
  refine ⟨Z,hZ,?_⟩
  intro N M hZM Q hQ hQN P hcontact p hdeg hp hann
  let R : PowerSeries K := ∑ i, (p i : PowerSeries K)*f i
  obtain ⟨n,hn,hcoeff,ho⟩ := horder p hdeg hp
  have hPP : (∑ i, (p i : PowerSeries K)*(P i : PowerSeries K)) = 0 := by
    have h := congrArg (Polynomial.coeToPowerSeries.ringHom : Polynomial K →+* PowerSeries K) hann
    simpa only [map_sum, map_mul, map_zero, Polynomial.coeToPowerSeries.ringHom_apply] using h
  have hid : (Q : PowerSeries K)*R =
      ∑ i, (p i : PowerSeries K)*((Q : PowerSeries K)*f i-(P i : PowerSeries K)) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hPP, sub_zero, R, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hc : seriesContact (N+M+1) ((Q : PowerSeries K)*R) := by
    rw [hid]
    exact seriesContact_sum Finset.univ _ _ (fun i _ => seriesContact_mul _ (hcontact i))
  have hQo : (Q : PowerSeries K).order ≤ (N : ℕ∞) := by
    have hlead : PowerSeries.coeff K Q.natDegree (Q : PowerSeries K) ≠ 0 := by
      simpa only [Polynomial.coeff_coe, Polynomial.coeff_natDegree] using
        Polynomial.leadingCoeff_ne_zero.mpr hQ
    exact (PowerSeries.order_le _ hlead).trans (by exact_mod_cast hQN)
  have hlow := PowerSeries.nat_le_order ((Q : PowerSeries K)*R) (N+M+1) hc
  rw [PowerSeries.order_mul] at hlow
  have hbad : ((N+M+1:ℕ):ℕ∞) ≤ ((N+n:ℕ):ℕ∞) := by
    exact hlow.trans (by simpa only [Nat.cast_add] using add_le_add hQo ho)
  have hbadNat : N+M+1 ≤ N+n := by exact_mod_cast hbad
  omega

end StrictEUnit
end
