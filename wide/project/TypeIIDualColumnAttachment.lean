import TypeIIDividedColumnContact
import PolynomialConnectionClearing
import Stage14RationalOrdinaryDerivation

/-! Exact attachment of the constructed minus-left polynomial recurrence to
SAME divided dual columns. No contact, rank or integrality is assumed here. -/
noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- The divided column has the expected successor after multiplication by
j+1. This uses constant-field linearity, not coefficient-field linearity. -/
theorem dualDividedColumn_succ_smul
    {k V : Type*} [Field k] [CharZero k] [AddCommGroup V] [Module k V]
    (D : Module.End k V) (P : V) (j : ℕ) :
    (j+1 : k) • dualDividedColumn D P (j+1) = D (dualDividedColumn D P j) := by
  have hj : (j+1 : k) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  have hf : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hs : (j+1 : k) * ((j+1).factorial : k)⁻¹ = (j.factorial : k)⁻¹ := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hj, hf]
  simp only [dualDividedColumn, pow_succ', Module.End.mul_apply,
    map_smul, smul_smul, hs]

/-- Exact SAME-data identity. No division by T is made, so even T=0 is
permitted when the literal clearing equation holds. -/
theorem typeIIDividedColumn_map_dual
    {K B : Type*} [Field K] [CharZero K] [Field B] [CharZero B] [Algebra K B]
    (d : Derivation K B B) (φ : Polynomial K →+* B)
    (hderiv : ∀ p : Polynomial K, d (φ p) = φ p.derivative)
    {r : ℕ} (T : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) B)
    (hclear : ∀ i l, φ (U i l) = φ T * A i l) :
    ∀ j i, φ (typeIIDividedColumn T U P j i) =
      (φ T)^j * dualDividedColumn (matrixDualColumn d A) (fun l => φ (P l)) j i := by
  classical
  let v := dualDividedColumn (matrixDualColumn d A) (fun l => φ (P l))
  intro j
  induction j with
  | zero =>
      intro i
      simp [typeIIDividedColumn, dualDividedColumn]
  | succ j ih =>
      intro i
      have hj : (j+1 : B) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
      have hr := congrArg φ (typeIIDividedColumn_succ T U P j i)
      have hc (n : ℕ) : φ (Polynomial.C (n : K)) = (n : B) := by
        simp only [Polynomial.C_eq_natCast, map_natCast]
      have hcj : φ (Polynomial.C (j+1 : K)) = (j+1 : B) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hc (j+1)
      simp only [map_mul, map_sub, map_sum, hc j, hcj] at hr
      have hd : φ ((typeIIDividedColumn T U P j i).derivative) =
          d ((φ T)^j * v j i) := by
        rw [← hderiv, ih]
      have hs : (∑ l, φ (U i l)*φ (typeIIDividedColumn T U P j l)) =
          (φ T)^(j+1) * ∑ l, A i l * v j l := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        rw [hclear, ih, pow_succ]
        ring
      have hv : (j+1 : B)*v (j+1) i = d (v j i) - ∑ l, A i l*v j l := by
        have he := congrFun (dualDividedColumn_succ_smul
          (matrixDualColumn d A) (fun l => φ (P l)) j) i
        change (j+1 : K) • v (j+1) i = d (v j i) - ∑ l, A i l*v j l at he
        simpa only [Algebra.smul_def, map_add, map_natCast, map_one] using he
      rw [hd, ih, hs, ← hderiv T] at hr
      apply mul_left_cancel₀ hj
      change (j+1 : B)*φ (typeIIDividedColumn T U P (j+1) i) =
        (j+1 : B)*((φ T)^(j+1)*v (j+1) i)
      rw [hr, Derivation.leibniz]
      simp only [smul_eq_mul]
      have hp := mul_derivation_pow d (φ T) j
      linear_combination (v j i)*hp - (φ T)^(j+1)*hv

/-- Canonical ordinary rational derivative: compatibility is PROVED from the
accepted Stage14 API, not an extra premise of the rational attachment. -/
theorem typeIIDividedColumn_ratFunc_dual
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (T : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      algebraMap (Polynomial K) (RatFunc K) T * A i l) :
    ∀ j i, algebraMap (Polynomial K) (RatFunc K) (typeIIDividedColumn T U P j i) =
      (algebraMap (Polynomial K) (RatFunc K) T)^j *
        dualDividedColumn (matrixDualColumn stage14_rationalOrdinaryDerivation A)
          (fun l => algebraMap (Polynomial K) (RatFunc K) (P l)) j i := by
  letI : CharZero (RatFunc K) := ⟨by
    intro m n h
    apply Nat.cast_injective (R := K)
    apply (algebraMap K (RatFunc K)).injective
    simpa only [map_natCast] using h⟩
  exact typeIIDividedColumn_map_dual stage14_rationalOrdinaryDerivation
    (algebraMap (Polynomial K) (RatFunc K))
    (fun p => stage14_rationalOrdinaryDerivation_polynomial p) T U P A hclear

end StrictEUnit
end
