import V5AnalyticJetGauge
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

theorem v5_extensionOrdinaryRationalMap_id_zero :
    v5_extensionOrdinaryRationalMap (RingHom.id K) (0 : K) =
      algebraMap (RatFunc K) (LaurentSeries K) := by
  ext1 q
  induction q using RatFunc.induction_on
  rename_i P Q hQ
  rw [map_div₀, map_div₀]
  congr 1 <;>
    rw [v5_extensionOrdinaryRationalMap_polynomial, RingHom.id_apply,
      Polynomial.map_id, ordinaryPointPolynomialSeries_coe, ordinaryPointPolynomialMap_apply,
      ordinaryPointPolynomialShift_apply, Polynomial.C_0, add_zero, Polynomial.comp_X,
      ← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 300000 in
/-- The rational gauge transports the same actual Laurent solution vector. -/
theorem v5_laurent_gauge_solution_vector
    (A R : Matrix ι ι (RatFunc K)) (hR : R.det ≠ 0)
    (y : ι → LaurentSeries K)
    (hy : ∀ i, laurentOrdinaryDerivation (y i) =
      (A.map (algebraMap (RatFunc K) (LaurentSeries K))).mulVec y i) :
    let z := (R.map (algebraMap (RatFunc K) (LaurentSeries K))).mulVec y
    ∀ i, laurentOrdinaryDerivation (z i) =
      ((v5RationalJetGauge A R).map (algebraMap (RatFunc K) (LaurentSeries K))).mulVec z i := by
  let φ := algebraMap (RatFunc K) (LaurentSeries K)
  let B := v5RatMatrixDerivative R + R*A
  have hprod :
      ∀ i, laurentOrdinaryDerivation ((φ.mapMatrix R).mulVec y i) =
        (φ.mapMatrix B).mulVec y i := by
    intro i
    rw [show φ.mapMatrix B = φ.mapMatrix (v5RatMatrixDerivative R) +
      φ.mapMatrix R * φ.mapMatrix A by simp only [B,map_add,map_mul],
      Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    change _ = (φ.mapMatrix (v5RatMatrixDerivative R)).mulVec y i +
      (φ.mapMatrix R).mulVec ((φ.mapMatrix A).mulVec y) i
    simp only [Matrix.mulVec, dotProduct, RingHom.mapMatrix_apply,
      Matrix.map_apply, map_sum, Derivation.leibniz, smul_eq_mul,
      stage14_rationalLaurent_differential, hy, v5RatMatrixDerivative,
      Finset.sum_add_distrib, φ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hR)
  have hBR : v5RationalJetGauge A R * R = B := by
    change B * R⁻¹ * R = B
    rw [mul_assoc,hRR,mul_one]
  dsimp only
  intro i
  change _ = (φ.mapMatrix (v5RationalJetGauge A R)).mulVec ((φ.mapMatrix R).mulVec y) i
  rw [Matrix.mulVec_mulVec, ← map_mul, hBR]
  exact hprod i

/-- Invertible rational changes of derivative coordinates preserve rational
linear independence. No algebraic independence between coordinates is needed. -/
theorem v5_laurent_gauge_linearIndependent
    (R : Matrix ι ι (RatFunc K)) (hR : R.det ≠ 0)
    (y : ι → LaurentSeries K) (hy : LinearIndependent (RatFunc K) y) :
    LinearIndependent (RatFunc K)
      ((R.map (algebraMap (RatFunc K) (LaurentSeries K))).mulVec y) := by
  have hl : Function.Injective (Fintype.linearCombination (RatFunc K) y) :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp hy
  have hr : LinearIndependent (RatFunc K) R :=
    Matrix.linearIndependent_rows_of_det_ne_zero hR
  have h := hr.map' (Fintype.linearCombination (RatFunc K) y) (LinearMap.ker_eq_bot.mpr hl)
  convert h using 1

/-- Coupled output for the literal selected derivatives of a scalar Laurent
solution: exact system, same selected order-zero coordinate and independence. -/
theorem v5_scalar_laurent_selected_jet_system {n : ℕ} (hn : 0 < n)
    (p : ℕ → Polynomial K) (hp : p n ≠ 0) (f : LaurentSeries K)
    (hf : ∑ j ∈ Finset.range (n+1), algebraMap (Polynomial K) (LaurentSeries K) (p j) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[j] f = 0)
    (hli : LinearIndependent (RatFunc K) (v5LaurentJet n f))
    (d : Fin n → ℕ)
    (hR : (v5SelectedCovariantRows (v5NormalizedScalarCompanion p n) ⟨0,hn⟩ d).det ≠ 0) :
    let A := v5NormalizedScalarCompanion p n
    let R := v5SelectedCovariantRows A ⟨0,hn⟩ d
    let z : Fin n → LaurentSeries K := fun i =>
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[d i] f
    LinearIndependent (RatFunc K) z ∧
      (∀ i, laurentOrdinaryDerivation (z i) =
        ((v5RationalJetGauge A R).map (algebraMap (RatFunc K) (LaurentSeries K))).mulVec z i) ∧
      (∀ i, d i = 0 → z i = f) := by
  let A := v5NormalizedScalarCompanion p n
  let R := v5SelectedCovariantRows A ⟨0,hn⟩ d
  let y := v5LaurentJet n f
  let φ := algebraMap (RatFunc K) (LaurentSeries K)
  let q : ℕ → LaurentSeries K := fun j => algebraMap (Polynomial K) (LaurentSeries K) (p j)
  have hmap : A.map φ = v5LaurentCompanion n q := by
    rw [v5_normalized_scalar_companion_map]
    have he : (fun j => φ (algebraMap (Polynomial K) (RatFunc K) (p j))) = q := by
      funext j
      exact (IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K) (p j)).symm
    rw [he]
  have hy : ∀ i, laurentOrdinaryDerivation (y i) = (A.map φ).mulVec y i := by
    rw [hmap]
    exact v5_laurent_jet_system n q
      (by simpa only [q,map_zero] using
        (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).ne hp) f hf
  have hz (i : Fin n) :
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[d i] f =
        (R.map φ).mulVec y i := by
    have h := v5_covariant_extension_row_iterate_eval (RingHom.id K) 0 A y
      (fun j => if j = (⟨0,hn⟩ : Fin n) then 1 else 0)
      (by
        rw [v5_extensionOrdinaryRationalMap_id_zero]
        exact hy) (d i)
    rw [v5_extensionOrdinaryRationalMap_id_zero] at h
    simpa only [apply_ite (algebraMap (RatFunc K) (LaurentSeries K)), map_one, map_zero,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      y, v5LaurentJet, Function.iterate_zero, id_eq] using h
  change LinearIndependent (RatFunc K) (fun i => _^[d i] f) ∧ _ ∧ _
  have hz' : (fun i => (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[d i] f) =
      (R.map φ).mulVec y := funext hz
  refine ⟨hz' ▸ v5_laurent_gauge_linearIndependent R hR y hli,
    ?_, fun i hi => by simp [hi]⟩
  intro i
  change _ = ((v5RationalJetGauge A R).map φ).mulVec (fun i => _^[d i] f) i
  rw [hz']
  exact v5_laurent_gauge_solution_vector A R hR y hy i

#print axioms v5_extensionOrdinaryRationalMap_id_zero
#print axioms v5_laurent_gauge_solution_vector
#print axioms v5_laurent_gauge_linearIndependent
#print axioms v5_scalar_laurent_selected_jet_system
end StrictEUnit
