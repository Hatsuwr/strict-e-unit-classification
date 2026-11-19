import RegularResidueFallingRows
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
The regular shear coefficients of the SAME cleared scalar companion.
Only integer powers of the original coordinate are removed. The original
clearing polynomial T is retained, and its trailing coefficient is not
replaced by a unit normalization of T. No spectral or solution-family
assumption is introduced. SOURCE ONLY until the separate serial replay.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The literal coefficient tail beginning at d, with no change of variable. -/
def polynomialTailPowerSeries {K : Type*} [CommSemiring K]
    (d : ℕ) (P : Polynomial K) : PowerSeries K :=
  PowerSeries.mk (fun k => P.coeff (k+d))

@[simp] theorem polynomialTailPowerSeries_constantCoeff
    {K : Type*} [CommSemiring K] (d : ℕ) (P : Polynomial K) :
    PowerSeries.constantCoeff K (polynomialTailPowerSeries d P)=P.coeff d := by
  simp only [polynomialTailPowerSeries,PowerSeries.constantCoeff_mk,Nat.zero_add]

/-- A supplied lower coefficient bound proves the literal tail factorization.
The zero-order case is included; no positivity of d is assumed. -/
theorem polynomialTailPowerSeries_factor
    {K : Type*} [CommSemiring K] (d : ℕ) (P : Polynomial K)
    (hP : ∀ k,k<d → P.coeff k=0) :
    (PowerSeries.X : PowerSeries K)^d*polynomialTailPowerSeries d P=
      (P : PowerSeries K) := by
  ext k
  rw [PowerSeries.coeff_X_pow_mul',Polynomial.coeff_coe]
  by_cases hdk : d≤k
  · rw [if_pos hdk]
    simp only [polynomialTailPowerSeries,PowerSeries.coeff_mk,Nat.sub_add_cancel hdk]
  · rw [if_neg hdk,hP k (Nat.lt_of_not_ge hdk)]

/-- The unit tail of the original T. This definition does not replace T. -/
def sameCompanionEulerDenominatorSeries {K : Type*} [Field K]
    (T : Polynomial K) : PowerSeries K :=
  polynomialTailPowerSeries T.natTrailingDegree T

/-- The shifted actual last-row numerator of the SAME U. -/
def sameCompanionEulerNumeratorSeries {K : Type*} [Field K] (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (j : Fin (n+1)) : PowerSeries K :=
  polynomialTailPowerSeries T.natTrailingDegree
    (Polynomial.X^(n+1-j.val)*U (Fin.last n) j)

/-- The power-series coefficient of the regular shear. Invert only the
nonzero-constant tail, keeping the original clearing polynomial in all identities. -/
def sameCompanionEulerLastRowSeries {K : Type*} [Field K] (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (j : Fin (n+1)) : PowerSeries K :=
  sameCompanionEulerNumeratorSeries n T U j*
    (sameCompanionEulerDenominatorSeries T)⁻¹

/-- The actual power-series Euler matrix of the regular integer shear.
The sparse matrix is written literally since PowerSeries K is not a field. -/
def sameCompanionEulerPowerSeriesMatrix {K : Type*} [Field K] (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K) :=
  Fin.lastCases (sameCompanionEulerLastRowSeries n T U)
    (fun i : Fin n => Pi.single i.succ (1 : PowerSeries K))+
      Matrix.diagonal (fun j => PowerSeries.C K (j.val:K))

@[simp] theorem sameCompanionEulerDenominatorSeries_constantCoeff
    {K : Type*} [Field K] (T : Polynomial K) :
    PowerSeries.constantCoeff K (sameCompanionEulerDenominatorSeries T)=
      T.coeff T.natTrailingDegree := by
  exact polynomialTailPowerSeries_constantCoeff _ _

theorem sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero
    {K : Type*} [Field K] (T : Polynomial K) (hT : T ≠ 0) :
    PowerSeries.constantCoeff K (sameCompanionEulerDenominatorSeries T) ≠ 0 := by
  rw [sameCompanionEulerDenominatorSeries_constantCoeff]
  exact Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT

theorem sameCompanionEulerDenominatorSeries_factor
    {K : Type*} [Field K] (T : Polynomial K) :
    (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*
      sameCompanionEulerDenominatorSeries T=(T : PowerSeries K) := by
  exact polynomialTailPowerSeries_factor _ _
    (fun k hk => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk)

/-- The regular inequalities force the whole shifted numerator below the
same original trailing order to vanish. Zero U entries impose no inequality. -/
theorem sameCompanionEuler_shifted_numerator_lower
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (j : Fin (n+1)) (k : ℕ) (hk : k<T.natTrailingDegree) :
    (Polynomial.X^(n+1-j.val)*U (Fin.last n) j).coeff k=0 := by
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hjk : n+1-j.val≤k
  · rw [if_pos hjk]
    by_cases hj : U (Fin.last n) j=0
    · rw [hj,Polynomial.coeff_zero]
    · have hb := hV j hj
      have hji := j.isLt
      exact Polynomial.coeff_eq_zero_of_lt_natTrailingDegree (by omega)
  · rw [if_neg hjk]

theorem sameCompanionEulerNumeratorSeries_factor
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (j : Fin (n+1)) :
    (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*
      sameCompanionEulerNumeratorSeries n T U j=
        ((Polynomial.X^(n+1-j.val)*U (Fin.last n) j : Polynomial K) : PowerSeries K) := by
  exact polynomialTailPowerSeries_factor _ _
    (sameCompanionEuler_shifted_numerator_lower n T U hV j)

/-- The guard is the existing guard in polynomialCompanionFace: a negative
putative feedback index contributes zero, not the coefficient at index zero. -/
@[simp] theorem sameCompanionEulerNumeratorSeries_constantCoeff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) :
    PowerSeries.constantCoeff K (sameCompanionEulerNumeratorSeries n T U j)=
      polynomialCompanionFace n 1 1 T U j := by
  simp only [sameCompanionEulerNumeratorSeries,polynomialTailPowerSeries_constantCoeff,
    Polynomial.coeff_X_pow_mul',polynomialCompanionFace,Polynomial.expand_one,
    Nat.one_mul,Nat.mul_one]

@[simp] theorem sameCompanionEulerLastRowSeries_constantCoeff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (j : Fin (n+1)) :
    PowerSeries.constantCoeff K (sameCompanionEulerLastRowSeries n T U j)=
      polynomialCompanionFace n 1 1 T U j/T.coeff T.natTrailingDegree := by
  rw [sameCompanionEulerLastRowSeries,map_mul,PowerSeries.constantCoeff_inv,
    sameCompanionEulerNumeratorSeries_constantCoeff,
    sameCompanionEulerDenominatorSeries_constantCoeff,div_eq_mul_inv]

/-- Literal clearing by the ORIGINAL T; its removed power is restored in the
identity. This includes T of trailing order zero. -/
theorem sameCompanionEulerLastRowSeries_clearing
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (j : Fin (n+1)) :
    (T : PowerSeries K)*sameCompanionEulerLastRowSeries n T U j=
      (PowerSeries.X : PowerSeries K)^(n+1-j.val)*(U (Fin.last n) j : PowerSeries K) := by
  let A := sameCompanionEulerDenominatorSeries T
  let N := sameCompanionEulerNumeratorSeries n T U j
  have hA : PowerSeries.constantCoeff K A ≠ 0 :=
    sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT
  have hTf : (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*A=
      (T : PowerSeries K) := sameCompanionEulerDenominatorSeries_factor T
  have hNf : (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*N=
      (PowerSeries.X : PowerSeries K)^(n+1-j.val)*(U (Fin.last n) j : PowerSeries K) := by
    simpa only [Polynomial.coe_mul,Polynomial.coe_pow,Polynomial.coe_X] using
      sameCompanionEulerNumeratorSeries_factor n T U hV j
  change (T : PowerSeries K)*(N*A⁻¹)=_
  rw [← hTf]
  calc
    _ = (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*N*(A*A⁻¹) := by ring
    _ = (PowerSeries.X : PowerSeries K)^T.natTrailingDegree*N := by
      rw [PowerSeries.mul_inv_cancel A hA,mul_one]
    _ = _ := hNf

/-- The constant term of the derived PS matrix is exactly the already
constructed regular companion residue, with the original trailing coefficient. -/
theorem sameCompanionEulerPowerSeriesMatrix_constantCoeff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    (sameCompanionEulerPowerSeriesMatrix n T U).map (PowerSeries.constantCoeff K)=
      regularCompanionResidue n (T.coeff T.natTrailingDegree)
        (polynomialCompanionFace n 1 1 T U) := by
  classical
  ext i j
  cases i using Fin.lastCases with
  | last =>
    by_cases hj : Fin.last n=j
    · subst j
      simp [sameCompanionEulerPowerSeriesMatrix,regularCompanionResidue,
        constantCompanion,Matrix.diagonal_apply]
    · simp [sameCompanionEulerPowerSeriesMatrix,regularCompanionResidue,
        constantCompanion,Matrix.diagonal_apply,hj]
  | cast i =>
    by_cases hj : i.castSucc=j
    · subst j
      simp [sameCompanionEulerPowerSeriesMatrix,regularCompanionResidue,
        constantCompanion,Matrix.diagonal_apply,Pi.single_apply]
    · simp [sameCompanionEulerPowerSeriesMatrix,regularCompanionResidue,
        constantCompanion,Matrix.diagonal_apply,Pi.single_apply,hj]

/-- Original clearing data identifies the sparse rows and derives all of the
regular PS coefficient identities for those SAME witnesses. No positivity of
the trailing order, unit-at-zero T, or spectrum assumption is supplied. -/
theorem sameClearing_regularEulerPowerSeries_coefficients
    {K : Type*} [Field K] (n : ℕ) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) :
    (∀ i : Fin n,∀ j,U i.castSucc j=(Pi.single i.succ T : Fin (n+1) → Polynomial K) j) ∧
    PowerSeries.constantCoeff K (sameCompanionEulerDenominatorSeries T) ≠ 0 ∧
    (∀ j,(T : PowerSeries K)*sameCompanionEulerLastRowSeries n T U j=
      (PowerSeries.X : PowerSeries K)^(n+1-j.val)*(U (Fin.last n) j : PowerSeries K)) ∧
    (sameCompanionEulerPowerSeriesMatrix n T U).map (PowerSeries.constantCoeff K)=
      regularCompanionResidue n (T.coeff T.natTrailingDegree)
        (polynomialCompanionFace n 1 1 T U) := by
  exact ⟨cleared_companion_shift_row n c T U hclear,
    sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT,
    sameCompanionEulerLastRowSeries_clearing n T U hT hV,
    sameCompanionEulerPowerSeriesMatrix_constantCoeff n T U⟩

end StrictEUnit
end
