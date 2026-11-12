import PowerSeriesEulerPochhammer

/-!
The literal scalar Euler action of the SAME regular companion. Every
power-series coefficient multiplies on the left. Restoring the ORIGINAL T
gives the original selected ordinary action times X^(n+1), and cancellation
uses only genuine nonzero factors. SOURCE ONLY until the serial replay.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The same regular scalar equation in its falling-Euler form. -/
def sameCompanionEulerScalarAction
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (f : PowerSeries K) : PowerSeries K :=
  weightedDerivativeJet (n+1) f-
    ∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*
      weightedDerivativeJet j.val f

/-- Exact signed expression for the ORIGINAL selected scalar tuple. -/
theorem sameCompanionPowerSeriesScalarAction_eq_last_sub
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (f : PowerSeries K) :
    sameCompanionPowerSeriesScalarAction n T U f=
      (T:PowerSeries K)*(PowerSeries.derivative K)^[n+1] f-
        ∑ j : Fin (n+1),(U (Fin.last n) j:PowerSeries K)*
          (PowerSeries.derivative K)^[j.val] f := by
  have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1))=Fin.last n := by
    apply Fin.ext
    simp
  unfold sameCompanionPowerSeriesScalarAction
  rw [Fin.sum_univ_castSucc]
  simp only [sameCompanionScalarTuple,Fin.lastCases_castSucc,Fin.lastCases_last,
    Fin.coe_castSucc,Fin.val_last,hidx,Polynomial.coe_neg,neg_mul]
  rw [Finset.sum_neg_distrib,add_comm,← sub_eq_add_neg]

/-- Restoring the ORIGINAL clearing polynomial identifies the two actual
actions on every power series, without any solution premise. -/
theorem sameCompanionEulerScalarAction_original_T
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    (T:PowerSeries K)*sameCompanionEulerScalarAction n T U f=
      (PowerSeries.X:PowerSeries K)^(n+1)*sameCompanionPowerSeriesScalarAction n T U f := by
  rw [sameCompanionEulerScalarAction,mul_sub,
    sameCompanionEuler_weighted_sum_clearing n T U hT hV f,
    sameCompanionPowerSeriesScalarAction_eq_last_sub]
  unfold weightedDerivativeJet
  ring

/-- The Euler scalar action and the ORIGINAL ordinary scalar action have
the same kernel. Neither T(0) nor an inverse of X is assumed. -/
theorem sameCompanionEulerScalarAction_eq_zero_iff_scalar
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    sameCompanionEulerScalarAction n T U f=0 ↔
      sameCompanionPowerSeriesScalarAction n T U f=0 := by
  have hTp : (T:PowerSeries K) ≠ 0 :=
    fun hz => hT (Polynomial.coe_eq_zero_iff.mp hz)
  have hX : (PowerSeries.X:PowerSeries K)^(n+1) ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  have hid := sameCompanionEulerScalarAction_original_T n T U hT hV f
  constructor
  · intro h
    rw [h,mul_zero] at hid
    exact (mul_eq_zero.mp hid.symm).resolve_left hX
  · intro h
    rw [h,mul_zero] at hid
    exact (mul_eq_zero.mp hid).resolve_left hTp

/-- The scalar Euler action is equivalent to the actual Euler matrix
equation on the literal weighted ordinary jets. -/
theorem sameCompanionEulerScalarAction_eq_zero_iff_euler_jets
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    sameCompanionEulerScalarAction n T U f=0 ↔
      ∀ i : Fin (n+1),powerSeriesEuler (weightedDerivativeJet i.val f)=
        (sameCompanionEulerPowerSeriesMatrix n T U *ᵥ
          (fun j => weightedDerivativeJet j.val f)) i := by
  exact (sameCompanionEulerScalarAction_eq_zero_iff_scalar n T U hT hV f).trans
    (sameCompanionPowerSeriesScalarAction_eq_zero_iff_euler n T U hT hV f)

/-- Only the CONSTANT-coefficient Pochhammer polynomials are evaluated at
the K-linear Euler map. The variable coefficients remain on the left. -/
theorem sameCompanionEulerScalarAction_eq_aevalPochhammer
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (f : PowerSeries K) :
    sameCompanionEulerScalarAction n T U f=
      Polynomial.aeval (powerSeriesEulerLinear (K := K)) (descPochhammer K (n+1)) f-
        ∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*
          Polynomial.aeval (powerSeriesEulerLinear (K := K)) (descPochhammer K j.val) f := by
  simp only [powerSeriesEulerLinear_descPochhammer,sameCompanionEulerScalarAction]

end StrictEUnit
end
