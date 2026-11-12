import SelectedEulerPowerSeriesCoefficients
import RegularResidueIndicialRoots
import LaurentOrdinaryDerivation

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

def laurentIntegerMonomial (d : ℤ) : LaurentSeries K := HahnSeries.single d (1:K)

@[simp] theorem laurentIntegerMonomial_mul (a b : ℤ) :
    laurentIntegerMonomial (K:=K) a*laurentIntegerMonomial b=laurentIntegerMonomial (a+b) := by
  simp only [laurentIntegerMonomial,HahnSeries.single_mul_single,one_mul]

@[simp] theorem laurentIntegerMonomial_zero : laurentIntegerMonomial (K:=K) 0=1 :=
  HahnSeries.single_zero_one

theorem laurentIntegerMonomial_ne_zero (d : ℤ) : laurentIntegerMonomial (K:=K) d ≠ 0 := by
  intro h
  have hc := congrArg (fun f : LaurentSeries K => f.coeff d) h
  have h10 : (1:K)=0 := by
    simpa only [laurentIntegerMonomial,HahnSeries.coeff_single_same,HahnSeries.coeff_zero] using hc
  exact one_ne_zero h10

/-- Actual Euler differentiation is coordinate times the actual ordinary
Laurent derivation, with no analytic or solution premise. -/
theorem laurentEuler_eq_coordinate_mul_ordinary (f : LaurentSeries K) :
    laurentEuler f=laurentIntegerMonomial 1*laurentOrdinaryDerivation f := by
  change laurentEuler f=laurentIntegerMonomial 1*(laurentIntegerMonomial (-1)*laurentEuler f)
  rw [← mul_assoc,laurentIntegerMonomial_mul]
  simp

theorem laurentEuler_nat_monomial (j : ℕ) :
    laurentEuler (laurentIntegerMonomial (K:=K) (j:ℤ))=
      (j:LaurentSeries K)*laurentIntegerMonomial (j:ℤ) := by
  rw [← map_natCast (HahnSeries.C : K →+* LaurentSeries K) j,HahnSeries.C_apply]
  unfold laurentIntegerMonomial
  rw [HahnSeries.single_mul_single]
  ext k
  simp only [laurentEuler_coeff,HahnSeries.coeff_single,zero_add,mul_one]
  split_ifs with h
  · subst k
    simp
  · simp

/-- Exact diagonal integer-shear differential formula for every Laurent
input, including arbitrary poles and not merely rational functions. -/
theorem laurentEuler_integer_shear_step (j : ℕ) (f : LaurentSeries K) :
    laurentEuler (laurentIntegerMonomial (j:ℤ)*f)=
      (j:LaurentSeries K)*(laurentIntegerMonomial (j:ℤ)*f)+
        laurentIntegerMonomial ((j+1:ℕ):ℤ)*laurentOrdinaryDerivation f := by
  rw [laurentEuler_mul,laurentEuler_nat_monomial,laurentEuler_eq_coordinate_mul_ordinary]
  have hm : laurentIntegerMonomial (K:=K) (j:ℤ)*laurentIntegerMonomial 1=
      laurentIntegerMonomial ((j+1:ℕ):ℤ) := by
    rw [laurentIntegerMonomial_mul]
    simp only [Nat.cast_add,Nat.cast_one]
  rw [mul_assoc,← mul_assoc (laurentIntegerMonomial (j:ℤ)) (laurentIntegerMonomial 1),hm]

def companionLaurentShear (n : ℕ) (v : Fin (n+1) → LaurentSeries K) : Fin (n+1) → LaurentSeries K :=
  fun j => laurentIntegerMonomial (j.val:ℤ)*v j

def companionLaurentUnshear (n : ℕ) (v : Fin (n+1) → LaurentSeries K) : Fin (n+1) → LaurentSeries K :=
  fun j => laurentIntegerMonomial (-(j.val:ℤ))*v j

@[simp] theorem companionLaurentShear_unshear (n : ℕ) (v : Fin (n+1) → LaurentSeries K) :
    companionLaurentShear n (companionLaurentUnshear n v)=v := by
  funext j
  simp only [companionLaurentShear,companionLaurentUnshear,← mul_assoc,
    laurentIntegerMonomial_mul,add_neg_cancel,laurentIntegerMonomial_zero,one_mul]

@[simp] theorem companionLaurentUnshear_shear (n : ℕ) (v : Fin (n+1) → LaurentSeries K) :
    companionLaurentUnshear n (companionLaurentShear n v)=v := by
  funext j
  simp only [companionLaurentShear,companionLaurentUnshear,← mul_assoc,
    laurentIntegerMonomial_mul,neg_add_cancel,laurentIntegerMonomial_zero,one_mul]

/-- Embed the actually constructed PS Euler matrix, not a new system. -/
def sameCompanionLaurentEulerMatrix (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    Matrix (Fin (n+1)) (Fin (n+1)) (LaurentSeries K) :=
  (sameCompanionEulerPowerSeriesMatrix n T U).map (HahnSeries.ofPowerSeries ℤ K)

theorem sameCompanionLaurentEulerMatrix_eq (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    sameCompanionLaurentEulerMatrix n T U=
      constantCompanion n (1:LaurentSeries K)
        (fun j => HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j))+
      Matrix.diagonal (fun j => (j.val:LaurentSeries K)) := by
  classical
  ext i j
  cases i using Fin.lastCases with
  | last =>
    by_cases hj : Fin.last n=j
    · subst j
      simp [sameCompanionLaurentEulerMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply]
    · simp [sameCompanionLaurentEulerMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply,hj]
  | cast i =>
    by_cases hj : i.castSucc=j
    · subst j
      simp [sameCompanionLaurentEulerMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply,Pi.single_apply]
    · simp [sameCompanionLaurentEulerMatrix,sameCompanionEulerPowerSeriesMatrix,
        constantCompanion,Matrix.diagonal_apply,Pi.single_apply,hj]

theorem sameCompanionLaurentEulerMatrix_mulVec (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (Y : Fin (n+1) → LaurentSeries K) :
    (sameCompanionLaurentEulerMatrix n T U *ᵥ Y) (Fin.last n)=
      (∑ j,HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)*Y j)+
        (n:LaurentSeries K)*Y (Fin.last n) ∧
    ∀ i : Fin n,(sameCompanionLaurentEulerMatrix n T U *ᵥ Y) i.castSucc=
      Y i.succ+(i.val:LaurentSeries K)*Y i.castSucc := by
  classical
  rw [sameCompanionLaurentEulerMatrix_eq,Matrix.add_mulVec]
  have hc := constantCompanion_column_action n (1:LaurentSeries K)
    (fun j => HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)) Y
  constructor
  · simpa only [Pi.add_apply,Matrix.mulVec_diagonal,Fin.val_last] using congrArg
      (fun z : LaurentSeries K => z+(n:LaurentSeries K)*Y (Fin.last n)) hc.1
  · intro i
    simpa only [Pi.add_apply,Matrix.mulVec_diagonal,Fin.coe_castSucc,one_mul] using congrArg
      (fun z : LaurentSeries K => z+(i.val:LaurentSeries K)*Y i.castSucc) (hc.2 i)

theorem sameCompanionEulerLastRowSeries_laurent_clearing (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1)) (j : Fin (n+1)) :
    HahnSeries.ofPowerSeries ℤ K (T:PowerSeries K)*
        HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)=
      laurentIntegerMonomial ((n+1-j.val:ℕ):ℤ)*
        HahnSeries.ofPowerSeries ℤ K (U (Fin.last n) j:PowerSeries K) := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ K)
    (sameCompanionEulerLastRowSeries_clearing n T U hT hV j)
  simpa only [map_mul,HahnSeries.ofPowerSeries_X_pow,laurentIntegerMonomial] using h

end StrictEUnit
end
