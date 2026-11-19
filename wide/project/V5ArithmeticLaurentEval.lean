import V5ArithmeticNormalization
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
namespace StrictEUnit

theorem V5ArithmeticMeromorphicZero.const (k : Subfield ℂ) (a : k) :
    V5ArithmeticMeromorphicZero k (fun _ => (a : ℂ)) :=
  V5ArithmeticMeromorphicZero.of_entire (algebraMap k (subfieldEntireFunctionAlgebra k) a)

theorem v5_arithmetic_laurent_monomial (k : Subfield ℂ) (a : k) (m : ℤ) :
    V5ArithmeticMeromorphicZero k (fun z => (a : ℂ) * (z : ℂ)^m) := by
  have hnonneg : 0 ≤ (m.natAbs : ℤ) + m := by
    cases m with
    | ofNat n => simp
    | negSucc n => simp; omega
  let d := ((m.natAbs : ℤ) + m).toNat
  have hd : (d : ℤ) = (m.natAbs : ℤ) + m := Int.toNat_of_nonneg hnonneg
  refine ⟨m.natAbs, (subfieldEntireCoordinate k)^d *
    algebraMap k (subfieldEntireFunctionAlgebra k) a, fun z => ?_⟩
  change (z : ℂ)^d * (a : ℂ) = (z : ℂ)^m.natAbs*((a : ℂ)*(z : ℂ)^m)
  calc
    _ = ((z : ℂ)^m.natAbs * (z : ℂ)^m) * (a : ℂ) := by
      rw [← zpow_natCast (z : ℂ) m.natAbs, ← zpow_add₀ (Units.ne_zero z), ← hd, zpow_natCast]
    _ = _ := by ring

theorem v5_arithmetic_laurent_eval (k : Subfield ℂ) (p : LaurentPolynomial k) :
    V5ArithmeticMeromorphicZero k (fun z => LaurentPolynomial.eval₂ k.subtype z p) := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    have h : (fun z => LaurentPolynomial.eval₂ k.subtype z (a+b)) =
        (fun z => LaurentPolynomial.eval₂ k.subtype z a) +
        (fun z => LaurentPolynomial.eval₂ k.subtype z b) := by
      funext z
      exact (LaurentPolynomial.eval₂ k.subtype z).map_add a b
    rw [h]
    exact ha.add hb
  | C_mul_T m a =>
    have h : (fun z => LaurentPolynomial.eval₂ k.subtype z
        (LaurentPolynomial.C a * LaurentPolynomial.T m)) =
        (fun z : ℂˣ => (a : ℂ) * (z : ℂ)^m) := by
      funext z
      simp only [LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
      rfl
    rw [h]
    exact v5_arithmetic_laurent_monomial k a m

end StrictEUnit
#print axioms StrictEUnit.V5ArithmeticMeromorphicZero.const
#print axioms StrictEUnit.v5_arithmetic_laurent_monomial
#print axioms StrictEUnit.v5_arithmetic_laurent_eval
