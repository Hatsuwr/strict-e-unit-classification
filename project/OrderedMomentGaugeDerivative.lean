import ActualOrderedMomentIntertwining
import PowerSeriesEulerPochhammer

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

theorem finiteParallelVector_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →S) (hf : f 0=0) {r s : ℕ} (x : Fin r →R) (h : Fin s →R) :
    (fun i =>f (finiteParallelVector s x h i))=
      finiteParallelVector s (fun i =>f (x i)) (fun j =>f (h j)) := by
  unfold finiteParallelVector
  rw [parallelForcingVector_map]
  apply (parallelForcingVector_eq_iff _ _ _ _ s).mpr
  exact ⟨rfl,fun j hj =>by simp [hj]⟩

variable {K : Type*} [Field K] [CharZero K]

theorem orderedSystemGauge_euler (r s : ℕ) (V : Matrix (Fin s) (Fin s) K)
    (hV : IsUnit ((V.map (PowerSeries.C K)).det))
    (v : Fin (r+s) →PowerSeries K) :
    (fun i =>powerSeriesEuler (orderedSystemGauge r s (V.map (PowerSeries.C K)) hV v i))=
      orderedSystemGauge r s (V.map (PowerSeries.C K)) hV (fun i =>powerSeriesEuler (v i)) := by
  obtain ⟨⟨x,h⟩,he⟩ := (finiteParallelLinear_bijective (K:=PowerSeries K) r s).2 v
  change finiteParallelVector s x h=v at he
  rw [← he,orderedSystemGauge_apply,finiteParallelVector_map powerSeriesEuler
    (show powerSeriesEuler (0:PowerSeries K)=0 from powerSeriesEulerLinear.map_zero),orderedSystemGauge_apply]
  have hm : (fun i =>powerSeriesEuler ((V.map (PowerSeries.C K)).mulVec h i))=
      (V.map (PowerSeries.C K)).mulVec (fun i =>powerSeriesEuler (h i)) := by
    funext i
    change powerSeriesEulerLinear (∑ j,PowerSeries.C K (V i j)*h j)=_
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [PowerSeries.smul_eq_C_mul,powerSeriesEulerLinear_apply,Matrix.map_apply] using
      powerSeriesEulerLinear.map_smul (V i j) (h j)
  funext i
  cases i using Fin.addCases with
  | left i =>simp only [Fin.addCases_left]
  | right i =>simpa only [Fin.addCases_right] using congrFun hm i

theorem orderedSystemGauge_matrix_derivative_zero (r s : ℕ) (V : Matrix (Fin s) (Fin s) K)
    (hV : IsUnit ((V.map (PowerSeries.C K)).det)) :
    Matrix.of (fun i j =>powerSeriesEuler
      (LinearMap.toMatrix' (orderedSystemGauge r s (V.map (PowerSeries.C K)) hV).toLinearMap i j))=0 := by
  funext i j
  simp only [Matrix.of_apply,LinearMap.toMatrix'_apply,Matrix.zero_apply]
  have he := congrFun (orderedSystemGauge_euler r s V hV (Pi.single j 1 : Fin (r+s) →PowerSeries K)) i
  have hz : (fun i : Fin (r+s) =>powerSeriesEuler ((Pi.single j 1 : Fin (r+s) →PowerSeries K) i))=(0:Fin (r+s) →PowerSeries K) := by
    funext k
    by_cases hk : k=j
    · subst k
      simp only [Pi.single_eq_same,Pi.zero_apply]
      apply PowerSeries.ext
      intro m
      simp [powerSeriesEuler]
    · simp only [Pi.single_eq_of_ne hk,Pi.zero_apply]
      exact powerSeriesEulerLinear.map_zero
  rw [hz,map_zero] at he
  have hb : (Pi.single j 1 : Fin (r+s) →PowerSeries K)=(fun k =>if k=j then 1 else 0) := by
    funext k
    by_cases hk : k=j
    · subst k;simp
    · simp [hk,Pi.single_eq_of_ne hk]
  simpa only [hb,Pi.zero_apply] using he

end StrictEUnit
end
