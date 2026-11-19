import ParallelForcingIndexedAction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K R : Type*} [Field K] [CharZero K] [CommRing R]

theorem forcingEulerBlock_map {S T : Type*} [CommRing S] [CommRing T] {r : ℕ}
    (φ : S →+* T) (C : Matrix (Fin r) (Fin r) S) (g : Fin r → S) (u : S) :
    (forcingEulerBlock C g u).map φ = forcingEulerBlock (C.map φ) (fun i =>φ (g i)) (φ u) := by
  funext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [forcingEulerBlock,Matrix.map_apply]

theorem parallelForcingVector_add_mapped_column {r : ℕ}
    (φ : PowerSeries K →+* R) (x : Fin r → R) (h : ℕ → R)
    (g : Fin r → PowerSeries K) (a : R) (s : ℕ) :
    (fun i => parallelForcingVector x h s i + φ (zeroPaddedPowerSeriesColumn g s i) * a) =
      parallelForcingVector (fun i => x i+φ (g i)*a) h s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero => simp [parallelForcingVector,zeroPaddedPowerSeriesColumn]
    | succ i => exact congrFun ih i

/-- Arbitrary ring-valued solutions, notably Laurent series with polynomial
log coefficients. A field structure on that ring is neither assumed nor needed. -/
theorem finiteLaurentEulerMatrix_mapped_mul_parallel {r : ℕ}
    (φ : PowerSeries K →+* R)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K)
    (M : ℕ) (k : ℕ → ℤ) (x : Fin r → R) (h : ℕ → R) (s : ℕ) :
    ((finiteLaurentEulerMatrix C g M k s).map φ).mulVec (parallelForcingVector x h s) =
      parallelForcingVector
        (fun i => (C.map φ).mulVec x i + φ (g i) * ∑ j ∈ Finset.range s, h j)
        (fun j => φ (PowerSeries.C K (((M:ℤ)+k j):K)) * h j) s := by
  induction s with
  | zero => simp [finiteLaurentEulerMatrix,parallelForcingVector]
  | succ s ih =>
    rw [finiteLaurentEulerMatrix,forcingEulerBlock_map,parallelForcingVector,
      forcingEulerBlock_mulVec,ih]
    funext i
    cases i using Fin.cases with
    | zero => simp [parallelForcingVector,Int.cast_add]
    | succ i =>
      simp only [Fin.cases_succ]
      have he := congrFun (parallelForcingVector_add_mapped_column φ
        (fun i => (C.map φ).mulVec x i+φ (g i)*∑ j ∈ Finset.range s,h j)
        (fun j => φ (PowerSeries.C K (((M:ℤ)+k j):K))*h j) g (h s) s) i
      rw [add_comm,he]
      simp only [parallelForcingVector,Fin.cases_succ,Finset.sum_range_succ]
      congr 2
      funext j
      ring

theorem finiteLaurentEulerMatrix_mapped_equation_iff {r : ℕ}
    (φ : PowerSeries K →+* R) (D : R → R)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r → PowerSeries K)
    (M : ℕ) (k : ℕ → ℤ) (x : Fin r → R) (h : ℕ → R) (s : ℕ) :
    (∀ i,D (parallelForcingVector x h s i)=
      ((finiteLaurentEulerMatrix C g M k s).map φ).mulVec (parallelForcingVector x h s) i) ↔
      (∀ i,D (x i)=(C.map φ).mulVec x i+φ (g i)*∑ j ∈ Finset.range s,h j) ∧
      (∀ j,j<s →D (h j)=φ (PowerSeries.C K (((M:ℤ)+k j):K))*h j) := by
  rw [← funext_iff,parallelForcingVector_map,finiteLaurentEulerMatrix_mapped_mul_parallel,
    parallelForcingVector_eq_iff,funext_iff]

end StrictEUnit
end
