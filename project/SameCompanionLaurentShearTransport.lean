import CompanionLaurentShearBasics

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

def polynomialLaurentImage (P : Polynomial K) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (P:PowerSeries K)

theorem polynomialLaurentImage_ne_zero (T : Polynomial K) (hT : T ≠ 0) :
    polynomialLaurentImage T ≠ 0 := by
  intro hz
  have hps : (T:PowerSeries K)=0 :=
    (HahnSeries.ofPowerSeries_injective (Γ:=ℤ) (R:=K)) (hz.trans (map_zero _).symm)
  exact hT ((Polynomial.coe_eq_zero_iff).mp hps)

def SameClearedLaurentCompanionSystem (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (v : Fin (n+1) → LaurentSeries K) : Prop :=
  ∀ i,polynomialLaurentImage T*laurentOrdinaryDerivation (v i)=
    ∑ j,polynomialLaurentImage (U i j)*v j

def SameLaurentEulerSystem (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (v : Fin (n+1) → LaurentSeries K) : Prop :=
  ∀ i,laurentEuler (v i)=(sameCompanionLaurentEulerMatrix n T U *ᵥ v) i

theorem sameClearedLaurentCompanionSystem_sparse
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (v : Fin (n+1) → LaurentSeries K) :
    SameClearedLaurentCompanionSystem n T U v ↔
      (∀ i : Fin n,laurentOrdinaryDerivation (v i.castSucc)=v i.succ) ∧
      polynomialLaurentImage T*laurentOrdinaryDerivation (v (Fin.last n))=
        ∑ j,polynomialLaurentImage (U (Fin.last n) j)*v j := by
  classical
  have hsum (i : Fin n) : (∑ j,polynomialLaurentImage (U i.castSucc j)*v j)=
      polynomialLaurentImage T*v i.succ := by
    simp_rw [cleared_companion_shift_row n c T U hclear i]
    rw [Finset.sum_eq_single i.succ]
    · simp [polynomialLaurentImage,Pi.single_apply]
    · intro j hj hne
      simp [polynomialLaurentImage,Pi.single_apply,hne]
    · simp
  constructor
  · intro h
    refine ⟨?_,h (Fin.last n)⟩
    intro i
    apply mul_left_cancel₀ (polynomialLaurentImage_ne_zero T hT)
    exact (h i.castSucc).trans (hsum i)
  · rintro ⟨hshift,hlast⟩ i
    cases i using Fin.lastCases with
    | last => exact hlast
    | cast i => rw [hshift i,hsum i]

private theorem add_left_right_cancel {R : Type*} [AddCommGroup R] (a b c : R) :
    a+b=c+a ↔ b=c := by
  rw [add_comm c a,add_left_cancel_iff]

/-- Full differential gauge transport for EVERY Laurent vector, not just
rational inputs or preselected solution germs. Only integer monomials occur. -/
theorem sameCompanionLaurentShear_system_iff
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (v : Fin (n+1) → LaurentSeries K) :
    SameClearedLaurentCompanionSystem n T U v ↔
      SameLaurentEulerSystem n T U (companionLaurentShear n v) := by
  classical
  let Z := companionLaurentShear n v
  let a : Fin (n+1) → LaurentSeries K := fun j =>
    HahnSeries.ofPowerSeries ℤ K (sameCompanionEulerLastRowSeries n T U j)
  let W : LaurentSeries K := laurentIntegerMonomial ((n+1:ℕ):ℤ)
  have hW : W ≠ 0 := laurentIntegerMonomial_ne_zero _
  have hTL := polynomialLaurentImage_ne_zero T hT
  have hterm (j : Fin (n+1)) : polynomialLaurentImage T*(a j*Z j)=
      W*(polynomialLaurentImage (U (Fin.last n) j)*v j) := by
    have hc := sameCompanionEulerLastRowSeries_laurent_clearing n T U hT hV j
    change polynomialLaurentImage T*a j=
      laurentIntegerMonomial ((n+1-j.val:ℕ):ℤ)*polynomialLaurentImage (U (Fin.last n) j) at hc
    have hi : ((n+1-j.val:ℕ):ℤ)+(j.val:ℤ)=((n+1:ℕ):ℤ) := by
      exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt j.isLt)
    change polynomialLaurentImage T*(a j*(laurentIntegerMonomial (j.val:ℤ)*v j))=_
    calc
      _ = (polynomialLaurentImage T*a j)*(laurentIntegerMonomial (j.val:ℤ)*v j) := by ring
      _ = (laurentIntegerMonomial ((n+1-j.val:ℕ):ℤ)*
          polynomialLaurentImage (U (Fin.last n) j))*(laurentIntegerMonomial (j.val:ℤ)*v j) := by rw [hc]
      _ = (laurentIntegerMonomial ((n+1-j.val:ℕ):ℤ)*laurentIntegerMonomial (j.val:ℤ))*
          (polynomialLaurentImage (U (Fin.last n) j)*v j) := by ring
      _ = _ := by rw [laurentIntegerMonomial_mul,hi]
  have hsum : polynomialLaurentImage T*(∑ j,a j*Z j)=
      W*(∑ j,polynomialLaurentImage (U (Fin.last n) j)*v j) := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j hj => hterm j)
  have hlast : W*laurentOrdinaryDerivation (v (Fin.last n))=(∑ j,a j*Z j) ↔
      polynomialLaurentImage T*laurentOrdinaryDerivation (v (Fin.last n))=
        ∑ j,polynomialLaurentImage (U (Fin.last n) j)*v j := by
    constructor
    · intro h
      apply mul_left_cancel₀ hW
      calc
        _ = polynomialLaurentImage T*(W*laurentOrdinaryDerivation (v (Fin.last n))) := by ring
        _ = polynomialLaurentImage T*(∑ j,a j*Z j) := congrArg (fun z => polynomialLaurentImage T*z) h
        _ = _ := hsum
    · intro h
      apply mul_left_cancel₀ hTL
      calc
        _ = W*(polynomialLaurentImage T*laurentOrdinaryDerivation (v (Fin.last n))) := by ring
        _ = W*(∑ j,polynomialLaurentImage (U (Fin.last n) j)*v j) := congrArg (fun z => W*z) h
        _ = _ := hsum.symm
  have hEuler : SameLaurentEulerSystem n T U Z ↔
      (∀ i : Fin n,laurentOrdinaryDerivation (v i.castSucc)=v i.succ) ∧
      W*laurentOrdinaryDerivation (v (Fin.last n))=(∑ j,a j*Z j) := by
    have hb := sameCompanionLaurentEulerMatrix_mulVec n T U Z
    have hz (i : Fin (n+1)) : laurentEuler (Z i)=
        (i.val:LaurentSeries K)*Z i+
          laurentIntegerMonomial ((i.val+1:ℕ):ℤ)*laurentOrdinaryDerivation (v i) :=
      laurentEuler_integer_shear_step i.val (v i)
    constructor
    · intro he
      refine ⟨?_,?_⟩
      · intro i
        have hi := he i.castSucc
        rw [hz i.castSucc,hb.2 i] at hi
        have h := (add_left_right_cancel _ _ _).mp hi
        change laurentIntegerMonomial ((i.val+1:ℕ):ℤ)*laurentOrdinaryDerivation (v i.castSucc)=
          laurentIntegerMonomial ((i.val+1:ℕ):ℤ)*v i.succ at h
        exact mul_left_cancel₀ (laurentIntegerMonomial_ne_zero _) h
      · have hi := he (Fin.last n)
        rw [hz (Fin.last n),hb.1] at hi
        exact (add_left_right_cancel _ _ _).mp hi
    · rintro ⟨hshift,hlast'⟩ i
      rw [hz i]
      cases i using Fin.lastCases with
      | last =>
        rw [hb.1]
        exact (add_left_right_cancel _ _ _).mpr hlast'
      | cast i =>
        rw [hb.2 i,hshift i]
        change (i.val:LaurentSeries K)*Z i.castSucc+
            laurentIntegerMonomial ((i.val+1:ℕ):ℤ)*v i.succ=
          Z i.succ+(i.val:LaurentSeries K)*Z i.castSucc
        rw [add_comm]
        rfl
  rw [sameClearedLaurentCompanionSystem_sparse n c T U hT hclear v,hEuler,hlast]

/-- Explicit inverse on ALL Laurent vectors: the integer diagonal is a
true Laurent gauge, with no fractional exponent extension. -/
theorem sameCompanionLaurentUnshear_system_iff
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j ≠ 0 →
      T.natTrailingDegree+j.val ≤ (U (Fin.last n) j).natTrailingDegree+(n+1))
    (Y : Fin (n+1) → LaurentSeries K) :
    SameLaurentEulerSystem n T U Y ↔
      SameClearedLaurentCompanionSystem n T U (companionLaurentUnshear n Y) := by
  simpa only [companionLaurentShear_unshear] using
    (sameCompanionLaurentShear_system_iff n c T U hT hclear hV (companionLaurentUnshear n Y)).symm

end StrictEUnit
end
