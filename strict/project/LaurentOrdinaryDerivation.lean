import LaurentEulerDerivation
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Actual ordinary formal differentiation on the Laurent-series field,
constructed from the proved Euler derivation. Compatibility concerns the
standard embedding of power series, not convergence of arbitrary series. -/
noncomputable section
namespace StrictEUnit
open HahnSeries
variable {k : Type*} [Field k]

/-- Multiplying the Euler derivation by t⁻¹ yields ordinary differentiation. -/
def laurentOrdinaryDerivation : Derivation k (LaurentSeries k) (LaurentSeries k) :=
  { toFun := fun f => HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler f
    map_add' := fun f g => by
      rw [show laurentEuler (f+g) = laurentEuler f + laurentEuler g from
        (laurentEulerLinear (k := k)).map_add f g, mul_add]
    map_smul' := fun c f => by
      ext n
      change (HahnSeries.single (-1 : ℤ) (1 : k) *
        laurentEuler (algebraMap k (LaurentSeries k) c * f)).coeff n = _
      simp only [RingHom.id_apply, HahnSeries.coeff_smul, Pi.smul_apply, smul_eq_mul]
      conv_lhs => rw [show n = (n + 1) + (-1) by omega]
      conv_rhs => arg 2; rw [show n = (n + 1) + (-1) by omega]
      rw [HahnSeries.coeff_single_mul_add, HahnSeries.coeff_single_mul_add,
        one_mul, one_mul, laurentEuler_coeff, laurentEuler_coeff,
        LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
      change ((n + 1 : ℤ) : k) * (HahnSeries.single (0 : ℤ) c * f).coeff (n+1) =
        c * (((n + 1 : ℤ) : k) * f.coeff (n + 1))
      rw [show n+1 = (n+1)+0 by omega, HahnSeries.coeff_single_mul_add]
      simp only [add_zero]
      ring
    map_one_eq_zero' := by
      change HahnSeries.single (-1 : ℤ) (1 : k) * laurentEulerDerivation (k := k) 1 = 0
      rw [Derivation.map_one_eq_zero, mul_zero]
    leibniz' := fun f g => by
      change HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler (f*g) =
        f * (HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler g) +
        g * (HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler f)
      rw [laurentEuler_mul]
      ring }

theorem laurentOrdinaryDerivation_coeff (f : LaurentSeries k) (n : ℤ) :
    (laurentOrdinaryDerivation f).coeff n = ((n + 1 : ℤ) : k) * f.coeff (n + 1) := by
  change (HahnSeries.single (-1 : ℤ) (1 : k) * laurentEuler f).coeff n = _
  conv_lhs => rw [show n = (n + 1) + (-1) by omega]
  rw [HahnSeries.coeff_single_mul_add, one_mul, laurentEuler_coeff]

/-- The standard embedded power series has no negative Laurent coefficients. -/
theorem powerSeries_laurent_coeff_neg (f : PowerSeries k) (n : ℤ) (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ k f).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_notin_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = n at hm
  omega

/-- Ordinary Laurent differentiation agrees with the actual power-series
formal derivative on the standard embedding, including the negative indices. -/
theorem laurentOrdinaryDerivation_ofPowerSeries (f : PowerSeries k) :
    laurentOrdinaryDerivation (HahnSeries.ofPowerSeries ℤ k f) =
      HahnSeries.ofPowerSeries ℤ k (PowerSeries.derivative k f) := by
  ext n
  rw [laurentOrdinaryDerivation_coeff]
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [← Nat.cast_add_one, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_derivative]
    push_cast
    ring
  · have hn0 : n < 0 := lt_of_not_ge hn
    rw [powerSeries_laurent_coeff_neg _ n hn0]
    by_cases heq : n + 1 = 0
    · rw [heq, Int.cast_zero, zero_mul]
    · rw [powerSeries_laurent_coeff_neg _ (n + 1) (by omega), mul_zero]

/-- Compatibility persists under every finite derivative iteration. -/
theorem laurentOrdinaryDerivation_iterate_ofPowerSeries (f : PowerSeries k) (n : ℕ) :
    ((laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[n])
      (HahnSeries.ofPowerSeries ℤ k f) =
      HahnSeries.ofPowerSeries ℤ k (((PowerSeries.derivative k : PowerSeries k → PowerSeries k)^[n]) f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      laurentOrdinaryDerivation_ofPowerSeries]
end StrictEUnit
#print axioms StrictEUnit.laurentOrdinaryDerivation
#print axioms StrictEUnit.laurentOrdinaryDerivation_coeff
#print axioms StrictEUnit.powerSeries_laurent_coeff_neg
#print axioms StrictEUnit.laurentOrdinaryDerivation_ofPowerSeries
#print axioms StrictEUnit.laurentOrdinaryDerivation_iterate_ofPowerSeries
