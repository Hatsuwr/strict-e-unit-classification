import V5ScalarIndicialJet
import LaurentDerivativeConstants
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]

def v5LaurentMatrixDerivative (Y : Matrix ι ι (LaurentSeries K)) : Matrix ι ι (LaurentSeries K) :=
  fun i j => laurentOrdinaryDerivation (Y i j)

omit [CharZero K] [DecidableEq ι] in
theorem v5_laurent_matrix_product (Y Z : Matrix ι ι (LaurentSeries K)) :
    v5LaurentMatrixDerivative (Y*Z) =
      v5LaurentMatrixDerivative Y * Z + Y * v5LaurentMatrixDerivative Z := by
  funext i j
  simp only [v5LaurentMatrixDerivative, Matrix.mul_apply, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib, Matrix.add_apply]
  rw [add_comm]
  apply congrArg₂ (· + ·) _ rfl
  apply Finset.sum_congr rfl
  intro a ha
  exact mul_comm _ _

/-- Actual Laurent solution matrices differ by a literal constant matrix. -/
theorem v5_laurent_solution_matrix_span
    (A Y Z : Matrix ι ι (LaurentSeries K)) (hdet : Y.det ≠ 0)
    (hY : v5LaurentMatrixDerivative Y = A*Y)
    (hZ : v5LaurentMatrixDerivative Z = A*Z) :
    ∃ C : Matrix ι ι K, Z = Y * C.map (algebraMap K (LaurentSeries K)) := by
  obtain ⟨U,hU⟩ := (Matrix.isUnit_iff_isUnit_det Y).mpr (isUnit_iff_ne_zero.mpr hdet)
  subst Y
  let T := (↑U⁻¹ : Matrix ι ι (LaurentSeries K))*Z
  have hp : (U : Matrix ι ι (LaurentSeries K))*T = Z := by
    dsimp [T]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hd := v5_laurent_matrix_product (U : Matrix ι ι (LaurentSeries K)) T
  rw [hp, hZ, hY, mul_assoc, hp] at hd
  have hz : (U : Matrix ι ι (LaurentSeries K))*v5LaurentMatrixDerivative T = 0 :=
    add_eq_left.mp hd.symm
  have ht : v5LaurentMatrixDerivative T = 0 := by
    apply U.isUnit.mul_left_cancel
    simpa only [mul_zero] using hz
  have hc (i j : ι) : T i j = algebraMap K (LaurentSeries K) ((T i j).coeff 0) :=
    (laurentOrdinaryDerivation_eq_zero_iff_eq_constant _).mp
      (congrArg (fun M => M i j) ht)
  refine ⟨fun i j => (T i j).coeff 0, ?_⟩
  have he : Matrix.map (fun i j => (T i j).coeff 0) (algebraMap K (LaurentSeries K)) = T := by
    funext i j
    exact (hc i j).symm
  rw [he]
  dsimp [T]
  rw [← mul_assoc, Units.mul_inv, one_mul]

/-- Vector version: every solution of the same system is a constant linear
combination of the columns of a nonsingular fundamental matrix. -/
theorem v5_laurent_solution_vector_span
    (A Y : Matrix ι ι (LaurentSeries K)) (v : ι → LaurentSeries K)
    (hdet : Y.det ≠ 0)
    (hY : v5LaurentMatrixDerivative Y = A*Y)
    (hv : ∀ i, (laurentOrdinaryDerivation (k := K)) (v i) = (A.mulVec v) i) :
    ∃ c : ι → K, ∀ i, v i = ∑ j, Y i j * algebraMap K (LaurentSeries K) (c j) := by
  cases isEmpty_or_nonempty ι with
  | inl he =>
    letI := he
    exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩
  | inr hn =>
    letI := hn
    let j₀ : ι := Classical.choice hn
    let Z : Matrix ι ι (LaurentSeries K) := fun i _ => v i
    have hz : v5LaurentMatrixDerivative Z = A*Z := by
      funext i j
      exact hv i
    obtain ⟨C,hC⟩ := v5_laurent_solution_matrix_span A Y Z hdet hY hz
    refine ⟨fun j => C j j₀, ?_⟩
    intro i
    exact congrArg (fun M => M i j₀) hC

/-- Normalized companion over the actual Laurent field. -/
def v5LaurentCompanion (n : ℕ) (p : ℕ → LaurentSeries K) :
    Matrix (Fin n) (Fin n) (LaurentSeries K) :=
  fun i j => if i.val+1 < n then (if j.val = i.val+1 then 1 else 0)
    else -(p n)⁻¹ * p j.val

def v5LaurentJet (n : ℕ) (f : LaurentSeries K) : Fin n → LaurentSeries K :=
  fun i => (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[i.val] f

omit [CharZero K] in
/-- The scalar equation supplies all rows of its companion system. -/
theorem v5_laurent_jet_system (n : ℕ) (p : ℕ → LaurentSeries K)
    (hp : p n ≠ 0) (f : LaurentSeries K)
    (hf : ∑ j ∈ Finset.range (n+1), p j *
      (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j] f = 0) :
    ∀ i, laurentOrdinaryDerivation (v5LaurentJet n f i) =
      ((v5LaurentCompanion n p).mulVec (v5LaurentJet n f)) i := by
  intro i
  change laurentOrdinaryDerivation _ = ∑ j : Fin n, _
  by_cases hi : i.val+1 < n
  · let next : Fin n := ⟨i.val+1,hi⟩
    have he (j : Fin n) : j.val = i.val+1 ↔ j = next :=
      by
      change j.val = next.val ↔ j = next
      exact ⟨Fin.ext, fun h => congrArg Fin.val h⟩
    simp only [v5LaurentCompanion, hi, if_true, he, ite_mul, one_mul, zero_mul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact (Function.iterate_succ_apply' _ _ _).symm
  · have hin : i.val+1 = n := by omega
    rw [Finset.sum_range_succ] at hf
    have hsum : (∑ j : Fin n, p j.val *
        (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j.val] f) +
        p n * (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[n] f = 0 := by
      rw [Fin.sum_univ_eq_sum_range (fun j => p j * (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j] f)]
      exact hf
    simp only [v5LaurentCompanion, hi, if_false, v5LaurentJet]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    rw [← Function.iterate_succ_apply' (laurentOrdinaryDerivation (k := K)) i.val f, Nat.succ_eq_add_one, hin]
    have ht := congrArg (fun z : LaurentSeries K => (p n)⁻¹ * z) hsum
    dsimp only at ht
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ hp, one_mul, mul_zero] at ht
    exact eq_neg_of_add_eq_zero_right ht |>.trans (by ring)

/-- A nonzero jet Wronskian makes a scalar solution family span all formal
Laurent solutions, with coefficients in the literal constant field. -/
theorem v5_laurent_scalar_wronskian_span (n : ℕ) (hn : 0 < n)
    (p : ℕ → LaurentSeries K) (hp : p n ≠ 0)
    (u : Fin n → LaurentSeries K) (f : LaurentSeries K)
    (hu : ∀ k, ∑ j ∈ Finset.range (n+1), p j *
      (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j] (u k) = 0)
    (hf : ∑ j ∈ Finset.range (n+1), p j *
      (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j] f = 0)
    (hdet : Matrix.det (fun i j : Fin n => v5LaurentJet n (u j) i) ≠ 0) :
    ∃ c : Fin n → K, f = ∑ j, u j * algebraMap K (LaurentSeries K) (c j) := by
  let Y : Matrix (Fin n) (Fin n) (LaurentSeries K) := fun i j => v5LaurentJet n (u j) i
  have hY : v5LaurentMatrixDerivative Y = v5LaurentCompanion n p * Y := by
    funext i j
    exact v5_laurent_jet_system n p hp (u j) (hu j) i
  obtain ⟨c,hc⟩ := v5_laurent_solution_vector_span (v5LaurentCompanion n p) Y
    (v5LaurentJet n f) hdet hY (v5_laurent_jet_system n p hp f hf)
  refine ⟨c, ?_⟩
  simpa only [Y, v5LaurentJet, Function.iterate_zero, id_eq] using hc ⟨0,hn⟩

/-- Formal scalar power-series solutions are spanned whenever their embedded
jet Wronskian is nonzero. No convergence or ordinary-point assumption is used. -/
theorem v5_formal_scalar_wronskian_span (n : ℕ) (hn : 0 < n)
    (p : ℕ → Polynomial K) (hp : p n ≠ 0)
    (u : Fin n → PowerSeries K) (f : PowerSeries K)
    (hu : ∀ j, v5ScalarODE p (n+1) (u j) = 0)
    (hf : v5ScalarODE p (n+1) f = 0)
    (hdet : Matrix.det (fun i j : Fin n => HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.derivative K)^[i.val] (u j))) ≠ 0) :
    ∃ c : Fin n → K, f = ∑ j, u j * PowerSeries.C K (c j) := by
  let e := HahnSeries.ofPowerSeries ℤ K
  let q : ℕ → LaurentSeries K := fun j => e (p j : PowerSeries K)
  have hq : q n ≠ 0 := by
    intro hz
    have hz' : (p n : PowerSeries K) = 0 :=
      HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa only [q, e, map_zero] using hz)
    exact hp ((Polynomial.coe_injective K) (by simpa only [map_zero] using hz'))
  have hmap (g : PowerSeries K) (hg : v5ScalarODE p (n+1) g = 0) :
      ∑ j ∈ Finset.range (n+1), q j *
        (laurentOrdinaryDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[j] (e g) = 0 := by
    have hh := congrArg e hg
    simpa only [q, e, v5ScalarODE, map_sum, map_mul, map_zero,
      laurentOrdinaryDerivation_iterate_ofPowerSeries] using hh
  have hd : Matrix.det (fun i j : Fin n => v5LaurentJet n (e (u j)) i) ≠ 0 := by
    simpa only [e, v5LaurentJet, laurentOrdinaryDerivation_iterate_ofPowerSeries] using hdet
  obtain ⟨c,hc⟩ := v5_laurent_scalar_wronskian_span n hn q hq
    (fun j => e (u j)) (e f) (fun j => hmap (u j) (hu j)) (hmap f hf) hd
  refine ⟨c, HahnSeries.ofPowerSeries_injective (Γ := ℤ) ?_⟩
  simpa only [e, map_sum, map_mul, HahnSeries.ofPowerSeries_C,
    LaurentSeries.algebraMap_apply] using hc

#print axioms v5_formal_scalar_wronskian_span
#print axioms v5_laurent_jet_system
#print axioms v5_laurent_scalar_wronskian_span
#print axioms v5_laurent_solution_matrix_span
#print axioms v5_laurent_solution_vector_span
end StrictEUnit
