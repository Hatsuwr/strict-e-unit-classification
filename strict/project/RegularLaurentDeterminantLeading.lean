import LogFrameConstructedInverse

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- A Laurent series with no negative coefficients is represented by its
actual natural coefficient power series. This works over a coefficient ring. -/
theorem regularLaurent_eq_ofPowerSeries {R : Type*} [CommRing R]
    (s : LaurentSeries R) (hs : ∀ a,a<0 →s.coeff a=0) :
    HahnSeries.ofPowerSeries ℤ R (PowerSeries.mk (fun n =>s.coeff (n : ℤ)))=s := by
  apply HahnSeries.ext
  funext a
  by_cases ha : a<0
  · change ((PowerSeries.mk (fun n =>s.coeff (n : ℤ)) : PowerSeries R) : LaurentSeries R).coeff a=s.coeff a
    rw [PowerSeries.coeff_coe,if_pos ha,hs a ha]
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤a)
    rw [HahnSeries.ofPowerSeries_apply_coeff,PowerSeries.coeff_mk]

/-- The leading constant coefficient of a regular Laurent matrix determinant
is the determinant of its actual constant coefficients. -/
theorem regularLaurentMatrix_det_coeff_zero {R : Type*} [CommRing R] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries R))
    (hA : ∀ i j a,a<0 →(A i j).coeff a=0) :
    A.det.coeff 0=(Matrix.of (fun i j =>(A i j).coeff 0)).det := by
  let U : Matrix (Fin r) (Fin r) (PowerSeries R) := fun i j =>PowerSeries.mk (fun n =>(A i j).coeff (n : ℤ))
  have hU : (HahnSeries.ofPowerSeries ℤ R).mapMatrix U=A := by
    funext i j
    exact regularLaurent_eq_ofPowerSeries (A i j) (hA i j)
  have hdet : HahnSeries.ofPowerSeries ℤ R U.det=A.det := by
    rw [RingHom.map_det,hU]
  rw [← hdet]
  change (HahnSeries.ofPowerSeries ℤ R U.det).coeff ((0 : ℕ) : ℤ)=_
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [RingHom.map_det]
  congr 1


end StrictEUnit
end
