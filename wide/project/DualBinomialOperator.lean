import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic.FieldSimp

/-! SOURCE-ONLY. Constant-field linear operator core of the dual-binomial
identity. D and V need not commute. The literal matrix differential attachment
is separate: this file does not identify its tower with a supplied matrix. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
section Raw
variable {k M : Type*} [CommRing k] [AddCommGroup M] [Module k M]

/-- The operator on endomorphisms is left composition by D minus right
composition by V. Its powers act on id, not directly on the column. -/
def dualConnectionTower (D V : Module.End k M) (n : ℕ) : Module.End k M :=
  ((LinearMap.mulLeft k D + LinearMap.mulRight k (-V))^n) 1

@[simp] theorem dualConnectionTower_zero (D V : Module.End k M) :
    dualConnectionTower D V 0 = 1 := by
  simp [dualConnectionTower]

theorem dualConnectionTower_succ (D V : Module.End k M) (n : ℕ) :
    dualConnectionTower D V (n+1) =
      D * dualConnectionTower D V n - dualConnectionTower D V n * V := by
  simp only [dualConnectionTower, pow_succ', Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
    mul_neg, sub_eq_add_neg]

/-- A local sign identity, not a commutation claim about D and V. -/
theorem dual_neg_pow_apply (V : Module.End k M) (n : ℕ) (x : M) :
    ((-V)^n) x = (-1 : k)^n • ((V^n) x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', Module.End.mul_apply, LinearMap.neg_apply, ih,
      map_smul, neg_one_mul, neg_smul, smul_neg, smul_smul]

/-- Raw binomial identity from commuting LEFT and RIGHT multiplication. -/
theorem dualConnectionTower_binomial (D V : Module.End k M) (n : ℕ) (x : M) :
    dualConnectionTower D V n x =
      ∑ h ∈ Finset.range (n+1),
        ((-1 : k)^h * (n.choose h : k)) • ((D^(n-h)) ((V^h) x)) := by
  have hc : Commute (LinearMap.mulRight k (-V)) (LinearMap.mulLeft k D) := by
    change (LinearMap.mulRight k (-V)) * (LinearMap.mulLeft k D) =
      (LinearMap.mulLeft k D) * (LinearMap.mulRight k (-V))
    apply LinearMap.ext
    intro F
    change (D * F) * (-V) = D * (F * (-V))
    exact mul_assoc D F (-V)
  have hp := congrArg (fun F : Module.End k (Module.End k M) => F 1) (hc.add_pow n)
  have ht : dualConnectionTower D V n =
      ∑ h ∈ Finset.range (n+1), n.choose h • (D^(n-h) * (-V)^h) := by
    simpa only [dualConnectionTower, add_comm (LinearMap.mulRight k (-V)),
      LinearMap.sum_apply, Module.End.mul_apply, Module.End.natCast_apply,
      map_nsmul, LinearMap.pow_mulRight, LinearMap.pow_mulLeft,
      LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_one] using hp
  rw [ht]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    dual_neg_pow_apply, map_smul]
  apply Finset.sum_congr rfl
  intro h hh
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, mul_comm]
end Raw

section Divided
variable {k M : Type*} [Field k] [CharZero k] [AddCommGroup M] [Module k M]

def dualDividedColumn (V : Module.End k M) (x : M) (j : ℕ) : M :=
  (j.factorial : k)⁻¹ • ((V^j) x)

/-- Factorials are invertible in the constant field; D is only k-linear. -/
theorem dualConnectionTower_divided (D V : Module.End k M) (n : ℕ) (x : M) :
    (n.factorial : k)⁻¹ • dualConnectionTower D V n x =
      ∑ h ∈ Finset.range (n+1),
        ((-1 : k)^h / ((n-h).factorial : k)) •
          ((D^(n-h)) (dualDividedColumn V x h)) := by
  rw [dualConnectionTower_binomial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hnz : (n.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hhz : (h.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)
  have hnhz : ((n-h).factorial : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n-h))
  simp only [dualDividedColumn, map_smul, smul_smul]
  congr 1
  rw [Nat.cast_choose k (Nat.le_of_lt_succ (Finset.mem_range.mp hh))]
  field_simp [hnz, hhz, hnhz]
  <;> ring

/-- Divided dual iteration of a divided column yields the precise binomial
coefficient; no interchange of D with V is used. -/
theorem dualDividedColumn_shift (V : Module.End k M) (x : M) (j h : ℕ) :
    dualDividedColumn V (dualDividedColumn V x j) h =
      ((j+h).choose h : k) • dualDividedColumn V x (j+h) := by
  have hjz : (j.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hhz : (h.factorial : k) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero h)
  have hjhz : ((j+h).factorial : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j+h))
  simp only [dualDividedColumn, map_smul, smul_smul]
  rw [← Module.End.mul_apply, ← pow_add, Nat.add_comm h j]
  congr 1
  rw [Nat.cast_choose k (Nat.le_add_left h j), Nat.add_sub_cancel_right]
  field_simp [hjz, hhz, hjhz]
  <;> ring

/-- Exact shifted-column identity, with P_j=V^j(x)/j!. -/
theorem dualConnectionTower_divided_shifted (D V : Module.End k M)
    (n j : ℕ) (x : M) :
    (n.factorial : k)⁻¹ • dualConnectionTower D V n (dualDividedColumn V x j) =
      ∑ h ∈ Finset.range (n+1),
        (((-1 : k)^h * ((j+h).choose h : k)) / ((n-h).factorial : k)) •
          ((D^(n-h)) (dualDividedColumn V x (j+h))) := by
  rw [dualConnectionTower_divided]
  apply Finset.sum_congr rfl
  intro h hh
  rw [dualDividedColumn_shift, map_smul, smul_smul]
  congr 1
  ring

end Divided
end StrictEUnit
end
