import FormalFundamentalMatrixUnit
import DifferentialFrameCoordinates
import LaurentDerivativeConstants

/-! Formal ordinary systems have no Laurent poles. The fundamental frame and
constant coordinates are constructed, not supplied as extra hypotheses. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

theorem laurent_ordinary_system_solution_powerSeries
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (u : Fin r → LaurentSeries K)
    (hu : ∀ i, laurentOrdinaryDerivation (u i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * u j) :
    ∃ w : Fin r → PowerSeries K, ∀ i, HahnSeries.ofPowerSeries ℤ K (w i) = u i := by
  classical
  obtain ⟨W, hW0, hWd, hWu⟩ := exists_normalized_formal_fundamentalMatrix A
  rcases hWu with ⟨U, rfl⟩
  let φ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  let ψ : Matrix (Fin r) (Fin r) (PowerSeries K) →+*
      Matrix (Fin r) (Fin r) (LaurentSeries K) := φ.mapMatrix
  let H := ψ (U : Matrix (Fin r) (Fin r) (PowerSeries K))
  let J := ψ (↑U⁻¹ : Matrix (Fin r) (Fin r) (PowerSeries K))
  let C := ψ A
  let D : LaurentSeries K →+ LaurentSeries K := {
    toFun := fun x => laurentOrdinaryDerivation x
    map_zero' := (laurentOrdinaryDerivation (k := K)).map_zero
    map_add' := (laurentOrdinaryDerivation (k := K)).map_add }
  have hJ : J * H = 1 := by
    dsimp only [J, H]
    rw [← map_mul, Units.inv_mul, map_one]
  have hH : H * J = 1 := by
    dsimp only [H, J]
    rw [← map_mul, Units.mul_inv, map_one]
  have hdH : (fun i j => D (H i j)) = C * H := by
    calc
      _ = ψ ((U : Matrix (Fin r) (Fin r) (PowerSeries K)).map
          (PowerSeries.derivative K)) := by
        apply Matrix.ext
        intro i j
        exact laurentOrdinaryDerivation_ofPowerSeries
          ((U : Matrix (Fin r) (Fin r) (PowerSeries K)) i j)
      _ = C * H := by rw [hWd, map_mul]
  have hD : ∀ x y, D (x*y) = D x*y + x*D y := by
    intro x y
    change laurentOrdinaryDerivation (x*y) =
      laurentOrdinaryDerivation x*y + x*laurentOrdinaryDerivation y
    rw [Derivation.leibniz]
    simp only [smul_eq_mul]
    ring
  have hu' : (fun i => D (u i)) = C.mulVec u := by funext i; exact hu i
  have hf : (fun i j => D (H i j)) = C*H-H*(0 : Matrix (Fin r) (Fin r) (LaurentSeries K)) := by
    simpa only [Matrix.mul_zero, sub_zero] using hdH
  let v := J.mulVec u
  have hcoord := differentialFrame_coordinates D hD C 0 H J hJ hH hf u hu'
  change H.mulVec v = u ∧ (fun i => D (v i)) =
    (0 : Matrix (Fin r) (Fin r) (LaurentSeries K)).mulVec v at hcoord
  rcases hcoord with ⟨hv, hdv⟩
  have hz (j : Fin r) : laurentOrdinaryDerivation (v j) = 0 := by
    have hh := congrFun hdv j
    simpa only [Matrix.zero_mulVec, Pi.zero_apply] using hh
  let c : Fin r → K := fun j => (v j).coeff 0
  have hconst (j : Fin r) : v j = φ (PowerSeries.C K (c j)) := by
    calc
      v j = algebraMap K (LaurentSeries K) (c j) :=
        (laurentOrdinaryDerivation_eq_zero_iff_eq_constant (v j)).mp (hz j)
      _ = φ (PowerSeries.C K (c j)) := by
        change algebraMap K (LaurentSeries K) (c j) =
          HahnSeries.ofPowerSeries ℤ K (PowerSeries.C K (c j))
        rw [HahnSeries.ofPowerSeries_C, LaurentSeries.algebraMap_apply]
  refine ⟨fun i => ∑ j,
    (U : Matrix (Fin r) (Fin r) (PowerSeries K)) i j * PowerSeries.C K (c j), ?_⟩
  intro i
  change φ (∑ j,
    (U : Matrix (Fin r) (Fin r) (PowerSeries K)) i j * PowerSeries.C K (c j)) = u i
  calc
    _ = ∑ j, H i j * v j := by
      simp only [map_sum, map_mul]
      apply Finset.sum_congr rfl
      intro j _
      rw [hconst j]
      rfl
    _ = u i := congrFun hv i

theorem laurent_ordinary_system_solution_coeff_neg
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (u : Fin r → LaurentSeries K)
    (hu : ∀ i, laurentOrdinaryDerivation (u i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * u j) :
    ∀ i n, n < 0 → (u i).coeff n = 0 := by
  obtain ⟨w, hw⟩ := laurent_ordinary_system_solution_powerSeries A u hu
  intro i n hn
  rw [← hw i]
  exact powerSeries_laurent_coeff_neg (w i) n hn

/-- A normalized ordinary scalar recurrence cannot have a Laurent solution
with a pole. Its companion coefficients are constructed from the recurrence. -/
theorem laurent_ordinary_recurrence_solution_powerSeries
    {K : Type*} [Field K] [CharZero K] (r : ℕ) (hr : 0 < r)
    (b : Fin r → PowerSeries K) (f : LaurentSeries K)
    (hrec : ∑ i, HahnSeries.ofPowerSeries ℤ K (b i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f =
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[r] f) :
    ∃ w : PowerSeries K, HahnSeries.ofPowerSeries ℤ K w = f := by
  classical
  let A : Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
    if i.val+1<r then (if j.val=i.val+1 then 1 else 0) else b j
  let Y : Fin r → LaurentSeries K := fun i =>
    (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f
  have hs : ∀ i, laurentOrdinaryDerivation (Y i) =
      ∑ j, HahnSeries.ofPowerSeries ℤ K (A i j) * Y j := by
    intro i
    change laurentOrdinaryDerivation
      ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] f) = _
    rw [← Function.iterate_succ_apply'
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K) i.val f]
    by_cases hi : i.val+1<r
    · let j0 : Fin r := ⟨i.val+1, hi⟩
      rw [Finset.sum_eq_single j0]
      · simp only [A, if_pos hi, j0, if_true, map_one, one_mul, Y]
      · intro j hj hne
        have hv : j.val ≠ i.val+1 := by
          intro he
          exact hne (Fin.ext he)
        simp only [A, if_pos hi, if_neg hv, map_zero, zero_mul]
      · simp
    · have he : i.val+1=r := by omega
      simpa only [A, if_neg hi, Y, Nat.succ_eq_add_one, he] using hrec.symm
  obtain ⟨w, hw⟩ := laurent_ordinary_system_solution_powerSeries A Y hs
  exact ⟨w ⟨0, hr⟩, hw ⟨0, hr⟩⟩
end StrictEUnit
