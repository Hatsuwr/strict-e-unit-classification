import SelectedEulerPowerSeriesCoefficients
import SameCompanionScalarTuple
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
Literal differential transport from the SAME selected scalar tuple to its
regular power-series Euler connection. The coordinate powers are natural
integer powers, and the original clearing polynomial is retained. No positive
trailing order, spectrum, solution-family or unit-at-zero assumption is used.
SOURCE ONLY until the separate serial replay.
-/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

def powerSeriesEuler {K : Type*} [CommSemiring K]
    (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.X*PowerSeries.derivative K f

def weightedDerivativeJet {K : Type*} [CommSemiring K]
    (j : ℕ) (f : PowerSeries K) : PowerSeries K :=
  PowerSeries.X^j*(PowerSeries.derivative K)^[j] f

theorem powerSeriesEuler_X_pow_mul {K : Type*} [CommSemiring K]
    (j : ℕ) (f : PowerSeries K) :
    powerSeriesEuler ((PowerSeries.X : PowerSeries K)^j*f)=
      (j:PowerSeries K)*((PowerSeries.X : PowerSeries K)^j*f)+
        (PowerSeries.X : PowerSeries K)^(j+1)*PowerSeries.derivative K f := by
  cases j with
  | zero => simp [powerSeriesEuler]
  | succ j =>
    unfold powerSeriesEuler
    rw [(PowerSeries.derivative K).leibniz,
      (PowerSeries.derivative K).leibniz_pow,PowerSeries.derivative_X]
    simp only [smul_eq_mul,nsmul_eq_mul,Nat.succ_sub_one,mul_one]
    simp only [pow_succ]
    ring

/-- The actual ordinary jets obey the falling-Euler recurrence. -/
theorem weightedDerivativeJet_euler {K : Type*} [CommSemiring K]
    (j : ℕ) (f : PowerSeries K) :
    powerSeriesEuler (weightedDerivativeJet j f)=
      (j:PowerSeries K)*weightedDerivativeJet j f+weightedDerivativeJet (j+1) f := by
  simpa only [weightedDerivativeJet,Function.iterate_succ_apply'] using
    powerSeriesEuler_X_pow_mul j ((PowerSeries.derivative K)^[j] f)

/-- The original selected polynomial tuple, with its original signs and
ordinary derivative iterates. No Euler operator is selected in its place. -/
def sameCompanionPowerSeriesScalarAction {K : Type*} [Field K] (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (f : PowerSeries K) : PowerSeries K :=
  ∑ j : Fin (n+2),
    (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U j : PowerSeries K)*
      (PowerSeries.derivative K)^[j.val] f

/-- Both exact column-action cases of the literal regular PS matrix. -/
theorem sameCompanionEulerPowerSeriesMatrix_mulVec
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (Y : Fin (n+1) → PowerSeries K) :
    (sameCompanionEulerPowerSeriesMatrix n T U *ᵥ Y) (Fin.last n)=
      (∑ j,sameCompanionEulerLastRowSeries n T U j*Y j)+
        (n:PowerSeries K)*Y (Fin.last n) ∧
    ∀ i : Fin n,(sameCompanionEulerPowerSeriesMatrix n T U *ᵥ Y) i.castSucc=
      Y i.succ+(i.val:PowerSeries K)*Y i.castSucc := by
  classical
  let S : Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K) :=
    Fin.lastCases (sameCompanionEulerLastRowSeries n T U) (fun i : Fin n => Pi.single i.succ 1)
  have hB : sameCompanionEulerPowerSeriesMatrix n T U=
      S+Matrix.diagonal (fun j => (j.val:PowerSeries K)) := by
    simp only [sameCompanionEulerPowerSeriesMatrix,map_natCast]
    rfl
  rw [hB,Matrix.add_mulVec]
  constructor
  · simp only [Pi.add_apply,Matrix.mulVec_diagonal,Fin.val_last]
    congr 1
    change (∑ j,S (Fin.last n) j*Y j)=_
    simp only [S,Fin.lastCases_last]
  · intro i
    simp only [Pi.add_apply,Matrix.mulVec_diagonal,Fin.coe_castSucc]
    congr 1
    change (∑ j,S i.castSucc j*Y j)=Y i.succ
    simp [S,Pi.single_apply]

theorem sameCompanionPowerSeriesScalarAction_eq_zero_iff_last
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (f : PowerSeries K) :
    sameCompanionPowerSeriesScalarAction n T U f=0 ↔
      (T:PowerSeries K)*(PowerSeries.derivative K)^[n+1] f=
        ∑ j : Fin (n+1),(U (Fin.last n) j:PowerSeries K)*
          (PowerSeries.derivative K)^[j.val] f := by
  have hidx : (⟨n+1-1,by omega⟩ : Fin (n+1))=Fin.last n := by
    apply Fin.ext
    simp
  unfold sameCompanionPowerSeriesScalarAction
  rw [Fin.sum_univ_castSucc]
  simp only [sameCompanionScalarTuple,Fin.lastCases_castSucc,Fin.lastCases_last,
    Fin.coe_castSucc,Fin.val_last,hidx,Polynomial.coe_neg,neg_mul]
  rw [Finset.sum_neg_distrib,add_comm,← sub_eq_add_neg,sub_eq_zero]

/-- Restoring the ORIGINAL T in every last-row product gives precisely the
original cleared derivative sum, with one common coordinate factor. -/
theorem sameCompanionEuler_weighted_sum_clearing
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    (T:PowerSeries K)*(∑ j : Fin (n+1),
      sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f)=
      (PowerSeries.X:PowerSeries K)^(n+1)*
        (∑ j : Fin (n+1),(U (Fin.last n) j:PowerSeries K)*
          (PowerSeries.derivative K)^[j.val] f) := by
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hpow : (PowerSeries.X:PowerSeries K)^(n+1-j.val)*PowerSeries.X^j.val=
      (PowerSeries.X:PowerSeries K)^(n+1) := by
    rw [← pow_add,Nat.sub_add_cancel (Nat.le_of_lt j.isLt)]
  calc
    (T:PowerSeries K)*(sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f)=
        ((T:PowerSeries K)*sameCompanionEulerLastRowSeries n T U j)*
          PowerSeries.X^j.val*(PowerSeries.derivative K)^[j.val] f := by
      unfold weightedDerivativeJet
      ring
    _ = ((PowerSeries.X:PowerSeries K)^(n+1-j.val)*(U (Fin.last n) j:PowerSeries K))*
          PowerSeries.X^j.val*(PowerSeries.derivative K)^[j.val] f := by
      rw [sameCompanionEulerLastRowSeries_clearing n T U hT hV j]
    _ = ((PowerSeries.X:PowerSeries K)^(n+1-j.val)*PowerSeries.X^j.val)*
          ((U (Fin.last n) j:PowerSeries K)*(PowerSeries.derivative K)^[j.val] f) := by ring
    _ = _ := by rw [hpow]

/-- Cancelling only genuine nonzero factors relates the sheared last row to
the original scalar last row. No inverse coordinate is introduced in PS. -/
theorem sameCompanionEuler_last_equation_iff
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    weightedDerivativeJet (n+1) f=
      (∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f) ↔
    (T:PowerSeries K)*(PowerSeries.derivative K)^[n+1] f=
      ∑ j : Fin (n+1),(U (Fin.last n) j:PowerSeries K)*
        (PowerSeries.derivative K)^[j.val] f := by
  have hTp : (T:PowerSeries K) ≠ 0 := by
    exact fun hz => hT (Polynomial.coe_eq_zero_iff.mp hz)
  have hX : (PowerSeries.X:PowerSeries K)^(n+1) ≠ 0 :=
    pow_ne_zero _ PowerSeries.X_ne_zero
  have hs := sameCompanionEuler_weighted_sum_clearing n T U hT hV f
  constructor
  · intro h
    apply mul_left_cancel₀ hX
    calc
      (PowerSeries.X:PowerSeries K)^(n+1)*
          ((T:PowerSeries K)*(PowerSeries.derivative K)^[n+1] f)=
        (T:PowerSeries K)*weightedDerivativeJet (n+1) f := by
          unfold weightedDerivativeJet
          ring
      _ = _ := congrArg (fun z : PowerSeries K => (T:PowerSeries K)*z) h
      _ = _ := hs
  · intro h
    apply mul_left_cancel₀ hTp
    calc
      (T:PowerSeries K)*weightedDerivativeJet (n+1) f=
        (PowerSeries.X:PowerSeries K)^(n+1)*
          ((T:PowerSeries K)*(PowerSeries.derivative K)^[n+1] f) := by
            unfold weightedDerivativeJet
            ring
      _ = _ := congrArg (fun z : PowerSeries K => (PowerSeries.X:PowerSeries K)^(n+1)*z) h
      _ = _ := hs.symm

/-- Universal SAME-scalar equivalence with the Euler equation on its literal
weighted ordinary jets. No solution or shift-chain premise is supplied. -/
theorem sameCompanionPowerSeriesScalarAction_eq_zero_iff_euler
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (f : PowerSeries K) :
    sameCompanionPowerSeriesScalarAction n T U f=0 ↔
      ∀ i : Fin (n+1),powerSeriesEuler (weightedDerivativeJet i.val f)=
        (sameCompanionEulerPowerSeriesMatrix n T U *ᵥ
          (fun j => weightedDerivativeJet j.val f)) i := by
  rw [sameCompanionPowerSeriesScalarAction_eq_zero_iff_last]
  have hrows := sameCompanionEulerPowerSeriesMatrix_mulVec n T U
    (fun j => weightedDerivativeJet j.val f)
  constructor
  · intro h
    have hw := (sameCompanionEuler_last_equation_iff n T U hT hV f).2 h
    intro i
    cases i using Fin.lastCases with
    | last =>
      rw [weightedDerivativeJet_euler,hrows.1]
      change (n:PowerSeries K)*weightedDerivativeJet n f+weightedDerivativeJet (n+1) f=
        (∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f)+
          (n:PowerSeries K)*weightedDerivativeJet n f
      rw [hw]
      exact add_comm _ _
    | cast i =>
      rw [weightedDerivativeJet_euler,hrows.2 i]
      change (i.val:PowerSeries K)*weightedDerivativeJet i.val f+weightedDerivativeJet (i.val+1) f=
        weightedDerivativeJet (i.val+1) f+(i.val:PowerSeries K)*weightedDerivativeJet i.val f
      exact add_comm _ _
  · intro h
    have hl := h (Fin.last n)
    rw [weightedDerivativeJet_euler,hrows.1] at hl
    change (n:PowerSeries K)*weightedDerivativeJet n f+weightedDerivativeJet (n+1) f=
      (∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f)+
        (n:PowerSeries K)*weightedDerivativeJet n f at hl
    have hw : weightedDerivativeJet (n+1) f=
        ∑ j : Fin (n+1),sameCompanionEulerLastRowSeries n T U j*weightedDerivativeJet j.val f :=
      add_left_cancel (hl.trans (add_comm _ _))
    exact (sameCompanionEuler_last_equation_iff n T U hT hV f).1 hw

/-- Every PS Euler solution is forced by its zero coordinate to be the
literal weighted ordinary jet. This follows from the matrix's own shift rows. -/
theorem sameCompanionPowerSeriesEulerSolution_eq_jets
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (Y : Fin (n+1) → PowerSeries K)
    (hY : ∀ i,powerSeriesEuler (Y i)=(sameCompanionEulerPowerSeriesMatrix n T U *ᵥ Y) i) :
    ∀ i,Y i=weightedDerivativeJet i.val (Y 0) := by
  have hrows := sameCompanionEulerPowerSeriesMatrix_mulVec n T U Y
  intro i
  induction i using Fin.induction with
  | zero => simp [weightedDerivativeJet]
  | succ i ih =>
    change Y i.castSucc=weightedDerivativeJet i.val (Y 0) at ih
    have hs := hY i.castSucc
    rw [hrows.2 i] at hs
    simp only [ih,weightedDerivativeJet_euler,Fin.coe_castSucc] at hs
    have hh : weightedDerivativeJet (i.val+1) (Y 0)=Y i.succ :=
      add_left_cancel (hs.trans (add_comm _ _))
    simpa only [Fin.val_succ] using hh.symm

/-- The zero coordinate of every derived PS Euler solution solves exactly
the original selected scalar tuple. -/
theorem sameCompanionPowerSeriesEulerSolution_scalar
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (Y : Fin (n+1) → PowerSeries K)
    (hY : ∀ i,powerSeriesEuler (Y i)=(sameCompanionEulerPowerSeriesMatrix n T U *ᵥ Y) i) :
    sameCompanionPowerSeriesScalarAction n T U (Y 0)=0 := by
  have hj : Y=(fun i => weightedDerivativeJet i.val (Y 0)) :=
    funext (sameCompanionPowerSeriesEulerSolution_eq_jets n T U Y hY)
  apply (sameCompanionPowerSeriesScalarAction_eq_zero_iff_euler n T U hT hV (Y 0)).2
  have hs := hY
  rw [hj] at hs
  exact hs

end StrictEUnit
end
