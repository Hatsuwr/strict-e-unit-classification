import ConstantForcingPrefixArithmetic
import ConstantForcingPoleBounds

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Local operator arithmetic: linear pole growth and exponential COMMON
prefix denominators. This is not an arithmetic assertion about solutions. -/
def LaurentDividedConnectionArithmetic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) : Prop :=
  ∃ P : ℕ,∃ C : ℝ,1≤C ∧
    (∀ m i j l,l< -((P*m : ℕ) : ℤ) →
      (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A m i j/
        (m.factorial : LaurentSeries K)).coeff l=0) ∧
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤C^(N+1) ∧
      ∀ m,m≤N →∀ i j l,l≤(N : ℤ) →IsIntegral ℤ ((D : K)*
        (matrixConnectionSequence (stage14_laurentAlgebraDerivation (k:=K)) A m i j/
          (m.factorial : LaurentSeries K)).coeff l)

def LaurentForcingArithmetic {r : ℕ} (b : Fin r → LaurentSeries K) : Prop :=
  ∃ W : ℕ,∃ C : ℝ,1≤C ∧ (∀ j l,l< -(W : ℤ) →(b j).coeff l=0) ∧
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤C^(N+1) ∧
      ∀ j l,l≤(N : ℤ) →IsIntegral ℤ ((D : K)*(b j).coeff l)

/-- Proved closure under adjoining a constant forcing coordinate. No closure
axiom is used. The construction gives linear poles and a common exponential
prefix integer DA*DB*LCM(N)^2 with only a linear increase of input cutoff. -/
theorem constantForcingConnection_arithmetic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (hA : LaurentDividedConnectionArithmetic A) (hb : LaurentForcingArithmetic b) :
    LaurentDividedConnectionArithmetic (constantForcingConnection A b) := by
  obtain ⟨P,C,hC,hAlow,hAden⟩ := hA
  obtain ⟨W,H,hH,hblow,hbden⟩ := hb
  let B := (C*H)^(P+W+4)*(16 : ℝ)^2
  have hCH : 1≤C*H := one_le_mul_of_one_le_of_one_le hC hH
  have hB : 1≤B := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCH) (by norm_num)
  refine ⟨P+W+1,B,hB,constantForcingConnection_linear_poles A b P W hAlow hblow,?_⟩
  intro N
  let M := (P+W+3)*(N+1)
  have hNM : N≤M := by dsimp [M];nlinarith
  obtain ⟨DA,hDA,hDAb,hDAi⟩ := hAden M
  obtain ⟨DB,hDB,hDBb,hDBi⟩ := hbden M
  refine ⟨DA*DB*logJetLCM N^2,Nat.mul_pos (Nat.mul_pos hDA hDB) (pow_pos (logJetLCM_pos N) _),?_,?_⟩
  · have hAB : (DA : ℝ)*(DB : ℝ)≤((C*H)^(P+W+4))^(N+1) := by
      calc
        _ ≤ (C*H)^(M+1) := by
          rw [mul_pow]
          exact mul_le_mul hDAb hDBb (Nat.cast_nonneg _) (pow_nonneg (by linarith) _)
        _ ≤ _ := by
          rw [← pow_mul]
          apply pow_le_pow_right₀ hCH
          dsimp [M]
          nlinarith
    have hL : (logJetLCM N : ℝ)^2≤((16 : ℝ)^2)^(N+1) := by
      calc
        _ ≤ ((16 : ℝ)^N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (logJetLCM_real_le_sixteen_pow N) _
        _ = ((16 : ℝ)^2)^N := by rw [← pow_mul,← pow_mul];congr 1;ring
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.le_succ _)
    dsimp [B]
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,mul_pow]
    exact mul_le_mul hAB hL (by positivity) (by positivity)
  · exact constantForcingConnection_prefix_integral A b P W N DA DB
      (fun a ha =>hAlow a) hblow
      (fun a ha i j l hl =>hDAi a (ha.trans hNM) i j l hl) hDBi

/-- A fixed zero/one coordinate vector has trivial denominator arithmetic. -/
theorem constantForcing_unit_vector_arithmetic (r : ℕ) :
    LaurentForcingArithmetic (K:=K) (fun i : Fin r =>if i.val=0 then 1 else 0) := by
  refine ⟨0,1,le_rfl,?_,?_⟩
  · intro i l hl
    simp only [Nat.cast_zero,neg_zero] at hl
    change (if i.val=0 then (1 : LaurentSeries K) else 0).coeff l=0
    split_ifs <;> simp [HahnSeries.coeff_one,show l≠0 by omega]
  · intro N
    refine ⟨1,by decide,by simp,?_⟩
    intro i l hl
    simp only [Nat.cast_one,one_mul]
    split_ifs <;> simp only [HahnSeries.coeff_one,HahnSeries.coeff_zero]
    · split_ifs
      · exact isIntegral_one
      · exact isIntegral_zero
    · exact isIntegral_zero

/-- First adjoin P, then its successive derivatives in front. For degree d
this has d+1 forcing coordinates; the source block is never identified with
the Fourier order. -/
def polynomialForcingConnection {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K) :
    (d : ℕ) →Matrix (Fin ((r+1)+d)) (Fin ((r+1)+d)) (LaurentSeries K)
  | 0 =>constantForcingConnection A b
  | d+1 =>constantForcingConnection (polynomialForcingConnection A b d)
      (fun i =>if i.val=0 then 1 else 0)

/-- Every FIXED finite polynomial forcing chain inherits proved divided
connection arithmetic. This remains an operator theorem, not an assertion
that all local solutions possess strict coefficient arithmetic. -/
theorem polynomialForcingConnection_arithmetic {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (hA : LaurentDividedConnectionArithmetic A) (hb : LaurentForcingArithmetic b) (d : ℕ) :
    LaurentDividedConnectionArithmetic (polynomialForcingConnection A b d) := by
  induction d with
  | zero =>exact constantForcingConnection_arithmetic A b hA hb
  | succ d ih =>exact constantForcingConnection_arithmetic _ _ ih (constantForcing_unit_vector_arithmetic _)

end StrictEUnit
end
