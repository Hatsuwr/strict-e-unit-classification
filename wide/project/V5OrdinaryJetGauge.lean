import V5FormalWronskianSpan
import OrdinaryRegularDenominatorClearing
import RationalCovariantRow
import Mathlib.RingTheory.PowerSeries.Inverse

/-! A rational connection admitting a power-series fundamental matrix with
invertible constant matrix has an ordinary polynomial clearing. The local
fundamental matrix itself may live over an extension of the coefficient field. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem v5_denom_ne_zero_of_extension_series (e : K →+* L) (α : K)
    (φ : RatFunc K →+* LaurentSeries L)
    (hφ : ∀ p : Polynomial K, φ (algebraMap (Polynomial K) (RatFunc K) p) =
      HahnSeries.ofPowerSeries ℤ L (ordinaryPointPolynomialSeries (e α) (p.map e)))
    (q : RatFunc K) (s : PowerSeries L) (hs : HahnSeries.ofPowerSeries ℤ L s = φ q) :
    q.denom.eval α ≠ 0 := by
  have hid := congrArg φ (ratFunc_num_eq_denom_mul q)
  rw [map_mul, hφ, hφ, ← hs, ← map_mul] at hid
  have heq := HahnSeries.ofPowerSeries_injective (Γ := ℤ) hid
  have hval := congrArg (PowerSeries.constantCoeff L) heq
  simp only [map_mul, ordinaryPointPolynomialSeries_constantCoeff,
    Polynomial.eval_map, Polynomial.eval₂_at_apply] at hval
  intro hd
  have hn : q.num.eval α = 0 := by
    apply e.injective
    simpa [hd] using hval
  obtain ⟨a,b,hab⟩ := RatFunc.isCoprime_num_denom q
  have hz := congrArg (Polynomial.eval α) hab
  simp [hn,hd] at hz

theorem v5_powerSeries_jetMatrix_isUnit
    (W : Matrix ι ι (PowerSeries L))
    (hW : (W.map (PowerSeries.constantCoeff L)).det ≠ 0) : IsUnit W := by
  apply (Matrix.isUnit_iff_isUnit_det W).mpr
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  exact isUnit_iff_ne_zero.mpr hW

theorem v5_rational_connection_ordinary_of_series_fundamental
    (e : K →+* L) (α : K) (φ : RatFunc K →+* LaurentSeries L)
    (hφ : ∀ p : Polynomial K, φ (algebraMap (Polynomial K) (RatFunc K) p) =
      HahnSeries.ofPowerSeries ℤ L (ordinaryPointPolynomialSeries (e α) (p.map e)))
    (B : Matrix ι ι (RatFunc K)) (W : Matrix ι ι (PowerSeries L))
    (hW : (W.map (PowerSeries.constantCoeff L)).det ≠ 0)
    (hODE : v5LaurentMatrixDerivative (W.map (HahnSeries.ofPowerSeries ℤ L)) =
      B.map φ * W.map (HahnSeries.ofPowerSeries ℤ L)) :
    ∃ T : Polynomial K, T.eval α ≠ 0 ∧ ∃ U : Matrix ι ι (Polynomial K),
      ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) T * B i j := by
  let ψ := HahnSeries.ofPowerSeries ℤ L
  let DW : Matrix ι ι (PowerSeries L) := fun i j => PowerSeries.derivative L (W i j)
  have hDW : DW.map ψ = v5LaurentMatrixDerivative (W.map ψ) := by
    funext i j
    exact (laurentOrdinaryDerivation_ofPowerSeries (W i j)).symm
  obtain ⟨v,hv⟩ := v5_powerSeries_jetMatrix_isUnit W hW
  let V : Matrix ι ι (PowerSeries L) := ↑v⁻¹
  have hWV : W * V = 1 := by
    rw [← hv]
    exact v.mul_inv
  have hmapprod : (DW * V).map ψ = B.map φ := by
    rw [Matrix.map_mul, hDW, hODE, mul_assoc, ← Matrix.map_mul, hWV,
      Matrix.map_one, mul_one]
    · exact map_zero ψ
    · exact map_one ψ
  apply exists_ordinary_polynomial_matrix_clearing α B
  intro i j
  apply (ordinaryPointRationalMap_regular_iff_denom_eval_ne_zero α (B i j)).mpr
  exact v5_denom_ne_zero_of_extension_series e α φ hφ (B i j) ((DW * V) i j)
    (congrArg (fun M => M i j) hmapprod)


/-- Translate a rational function with coefficients mapped to a larger field. -/
def v5_extensionOrdinaryRationalMap (e : K →+* L) (α : K) :
    RatFunc K →+* LaurentSeries L :=
  RatFunc.liftRingHom ((ordinaryPointPolynomialMap (e α)).comp (Polynomial.mapRingHom e))
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
      ((ordinaryPointPolynomialMap_injective (e α)).comp (Polynomial.map_injective e e.injective)))

@[simp] theorem v5_extensionOrdinaryRationalMap_polynomial (e : K →+* L) (α : K)
    (p : Polynomial K) :
    v5_extensionOrdinaryRationalMap e α (algebraMap (Polynomial K) (RatFunc K) p) =
      HahnSeries.ofPowerSeries ℤ L (ordinaryPointPolynomialSeries (e α) (p.map e)) := by
  unfold v5_extensionOrdinaryRationalMap
  rw [show algebraMap (Polynomial K) (RatFunc K) p =
      algebraMap (Polynomial K) (RatFunc K) p /
        algebraMap (Polynomial K) (RatFunc K) 1 by simp, RatFunc.liftRingHom_apply_div]
  simp

theorem v5_extensionOrdinaryRationalMap_derivative (e : K →+* L) (α : K)
    (q : RatFunc K) :
    laurentOrdinaryDerivation (v5_extensionOrdinaryRationalMap e α q) =
      v5_extensionOrdinaryRationalMap e α (stage14_rationalOrdinaryDerivation q) := by
  induction q using RatFunc.induction_on
  rename_i P Q hQ
  rw [map_div₀, Derivation.leibniz_div, Derivation.leibniz_div,
    stage14_rationalOrdinaryDerivation_polynomial, stage14_rationalOrdinaryDerivation_polynomial]
  simp only [v5_extensionOrdinaryRationalMap_polynomial, ordinaryPointPolynomialSeries_coe,
    ordinaryPointPolynomialMap_derivative, Polynomial.derivative_map,
    smul_eq_mul, map_sub, map_mul, map_pow, map_div₀, map_inv₀]

def v5RatMatrixDerivative (A : Matrix ι ι (RatFunc K)) : Matrix ι ι (RatFunc K) :=
  fun i j => stage14_rationalOrdinaryDerivation (A i j)

def v5RationalJetGauge (A R : Matrix ι ι (RatFunc K)) : Matrix ι ι (RatFunc K) :=
  (v5RatMatrixDerivative R + R*A) * R⁻¹

/-- A full-rank ordinary jet chart gives an ordinary rational system even
if the original connection has a pole there. -/
theorem v5_rational_jetGauge_ordinary
    (e : K →+* L) (α : K) (A R : Matrix ι ι (RatFunc K))
    (Y : Matrix ι ι (LaurentSeries L)) (W : Matrix ι ι (PowerSeries L))
    (hY : v5LaurentMatrixDerivative Y = A.map (v5_extensionOrdinaryRationalMap e α) * Y)
    (hW : (W.map (PowerSeries.constantCoeff L)).det ≠ 0)
    (hRY : W.map (HahnSeries.ofPowerSeries ℤ L) =
      R.map (v5_extensionOrdinaryRationalMap e α) * Y) :
    R.det ≠ 0 ∧ ∃ T : Polynomial K, T.eval α ≠ 0 ∧
      ∃ U : Matrix ι ι (Polynomial K), ∀ i j,
      algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) T * v5RationalJetGauge A R i j := by
  let φ := v5_extensionOrdinaryRationalMap e α
  let ψ := HahnSeries.ofPowerSeries ℤ L
  have hdetW : ((W.map ψ).det) ≠ 0 := by
    change (ψ.mapMatrix W).det ≠ 0
    rw [← RingHom.map_det ψ W]
    exact (v5_powerSeries_jetMatrix_isUnit W hW |>.map Matrix.detMonoidHom |>.map ψ).ne_zero
  have hdetR : R.det ≠ 0 := by
    intro hzero
    apply hdetW
    change (W.map ψ).det = 0
    rw [hRY, Matrix.det_mul]
    change (φ.mapMatrix R).det * Y.det = 0
    rw [← RingHom.map_det φ R, hzero, map_zero, zero_mul]
  refine ⟨hdetR, v5_rational_connection_ordinary_of_series_fundamental e α φ
    (v5_extensionOrdinaryRationalMap_polynomial e α) _ W hW ?_⟩
  have hder : v5LaurentMatrixDerivative (R.map φ) = (v5RatMatrixDerivative R).map φ := by
    funext i j
    exact v5_extensionOrdinaryRationalMap_derivative e α (R i j)
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdetR)
  have hmapRR := congrArg φ.mapMatrix hRR
  rw [map_mul, map_one] at hmapRR
  have hmapRA := map_mul φ.mapMatrix R A
  have hmapB := (map_mul φ.mapMatrix (v5RatMatrixDerivative R + R*A) R⁻¹).trans
    (congrArg (fun M => M * φ.mapMatrix R⁻¹) (map_add φ.mapMatrix _ _))
  change v5LaurentMatrixDerivative (W.map ψ) = φ.mapMatrix (v5RationalJetGauge A R) * W.map ψ
  unfold v5RationalJetGauge
  rw [hRY, v5_laurent_matrix_product, hY, hder, hmapB, hmapRA]
  change _ = (φ.mapMatrix (v5RatMatrixDerivative R) + φ.mapMatrix R * φ.mapMatrix A) *
    φ.mapMatrix R⁻¹ * (φ.mapMatrix R * Y)
  rw [mul_assoc, ← mul_assoc (φ.mapMatrix R⁻¹), hmapRR, one_mul, add_mul, mul_assoc]
  rfl


/-- Covariant jets compute derivatives in the exact shifted extension field. -/
theorem v5_covariant_extension_row_iterate_eval {n : ℕ}
    (e : K →+* L) (α : K) (A : Matrix (Fin n) (Fin n) (RatFunc K))
    (y : Fin n → LaurentSeries L) (q : Fin n → RatFunc K)
    (hy : ∀ i, laurentOrdinaryDerivation (y i) =
      ∑ j, v5_extensionOrdinaryRationalMap e α (A i j) * y j) (m : ℕ) :
    (laurentOrdinaryDerivation : LaurentSeries L → LaurentSeries L)^[m]
      (∑ j, v5_extensionOrdinaryRationalMap e α (q j) * y j) =
      ∑ j, v5_extensionOrdinaryRationalMap e α
        (((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[m]) q j) * y j := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp only [map_sum, Derivation.leibniz, smul_eq_mul, hy,
      v5_extensionOrdinaryRationalMap_derivative, rationalCovariantRow,
      map_add, map_mul, add_mul, Finset.sum_add_distrib]
    rw [add_comm (∑ x, _ * ∑ j, _)]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro x hx
      exact mul_comm _ _
    · simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm

/-- Selected higher derivative rows of a scalar companion, expressed over the
original rational coefficient field. A retained derivative order zero is
literally the first coordinate, not just a rational multiple. -/
def v5SelectedCovariantRows {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RatFunc K)) (j₀ : Fin n) (d : Fin n → ℕ) :
    Matrix (Fin n) (Fin n) (RatFunc K) :=
  fun i => (rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[d i]
    (fun j => if j = j₀ then 1 else 0)

theorem v5_selected_covariant_zero_row {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (RatFunc K)) (j₀ : Fin n) (d : Fin n → ℕ)
    (i : Fin n) (hi : d i = 0) :
    v5SelectedCovariantRows A j₀ d i = fun j => if j = j₀ then 1 else 0 := by
  simp [v5SelectedCovariantRows, hi]

theorem v5_selected_formal_jets_equal_covariant_matrix {n : ℕ}
    (e : K →+* L) (α : K) (A : Matrix (Fin n) (Fin n) (RatFunc K))
    (j₀ : Fin n) (d : Fin n → ℕ) (u : Fin n → PowerSeries L)
    (Y : Matrix (Fin n) (Fin n) (LaurentSeries L))
    (hY : v5LaurentMatrixDerivative Y = A.map (v5_extensionOrdinaryRationalMap e α) * Y)
    (hu : ∀ j, Y j₀ j = HahnSeries.ofPowerSeries ℤ L (u j)) :
    (fun i j => HahnSeries.ofPowerSeries ℤ L ((PowerSeries.derivative L)^[d i] (u j))) =
      (v5SelectedCovariantRows A j₀ d).map (v5_extensionOrdinaryRationalMap e α) * Y := by
  funext i j
  change _ = ∑ t, v5_extensionOrdinaryRationalMap e α (v5SelectedCovariantRows A j₀ d i t) * Y t j
  rw [← laurentOrdinaryDerivation_iterate_ofPowerSeries, ← hu]
  have hh (t : Fin n) : laurentOrdinaryDerivation (Y t j) =
      ∑ s, v5_extensionOrdinaryRationalMap e α (A t s) * Y s j :=
    congrArg (fun M => M t j) hY
  have h := v5_covariant_extension_row_iterate_eval e α A (fun t => Y t j)
    (fun t => if t = j₀ then 1 else 0) hh (d i)
  simpa only [apply_ite (v5_extensionOrdinaryRationalMap e α), map_one, map_zero,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    v5SelectedCovariantRows] using h

/-- The selected power-series derivatives alone suffice to certify ordinary
clearing for the new, literally derivative-coordinate rational system. -/
theorem v5_selected_formal_jets_ordinary {n : ℕ}
    (e : K →+* L) (α : K) (A : Matrix (Fin n) (Fin n) (RatFunc K))
    (j₀ : Fin n) (d : Fin n → ℕ) (u : Fin n → PowerSeries L)
    (Y : Matrix (Fin n) (Fin n) (LaurentSeries L))
    (hY : v5LaurentMatrixDerivative Y = A.map (v5_extensionOrdinaryRationalMap e α) * Y)
    (hu : ∀ j, Y j₀ j = HahnSeries.ofPowerSeries ℤ L (u j))
    (hdet : Matrix.det (fun i j : Fin n => PowerSeries.constantCoeff L
      ((PowerSeries.derivative L)^[d i] (u j))) ≠ 0) :
    let R := v5SelectedCovariantRows A j₀ d
    R.det ≠ 0 ∧ ∃ T : Polynomial K, T.eval α ≠ 0 ∧
      ∃ U : Matrix (Fin n) (Fin n) (Polynomial K), ∀ i j,
      algebraMap (Polynomial K) (RatFunc K) (U i j) =
        algebraMap (Polynomial K) (RatFunc K) T * v5RationalJetGauge A R i j :=
  v5_rational_jetGauge_ordinary e α A (v5SelectedCovariantRows A j₀ d)
    Y (fun i j => (PowerSeries.derivative L)^[d i] (u j)) hY hdet
    (v5_selected_formal_jets_equal_covariant_matrix e α A j₀ d u Y hY hu)

#print axioms v5_covariant_extension_row_iterate_eval
#print axioms v5_selected_covariant_zero_row
#print axioms v5_selected_formal_jets_equal_covariant_matrix
#print axioms v5_selected_formal_jets_ordinary
#print axioms v5_extensionOrdinaryRationalMap_derivative
#print axioms v5_rational_jetGauge_ordinary

#print axioms v5_denom_ne_zero_of_extension_series
#print axioms v5_powerSeries_jetMatrix_isUnit
#print axioms v5_rational_connection_ordinary_of_series_fundamental
end StrictEUnit
