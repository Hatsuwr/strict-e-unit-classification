import Stage14LaurentPolynomialODEClosure
import Stage41StrictSeriesRealization

/-! NEW, SOURCE-ONLY, UNCOMPILED. Signed coefficient transform, not a ring
homomorphism. No source annihilator, regularity, or arithmetic family is claimed. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def signedInverseLaplace (y : LaurentSeries K) : PowerSeries K :=
  PowerSeries.mk fun n => (-1 : K)^n * y.coeff ((n : ℤ)+1) / (n.factorial : K)

theorem signedInverseLaplace_coeff (y : LaurentSeries K) (n : ℕ) :
    PowerSeries.coeff K n (signedInverseLaplace y) =
      (-1 : K)^n * y.coeff ((n : ℤ)+1) / (n.factorial : K) :=
  PowerSeries.coeff_mk _ _

theorem signedInverseLaplace_zero : signedInverseLaplace (0 : LaurentSeries K) = 0 := by
  ext n
  simp only [signedInverseLaplace_coeff, HahnSeries.coeff_zero, mul_zero, zero_div, map_zero]

theorem signedInverseLaplace_add (y z : LaurentSeries K) :
    signedInverseLaplace (y+z) = signedInverseLaplace y + signedInverseLaplace z := by
  ext n
  simp only [signedInverseLaplace_coeff, HahnSeries.coeff_add, map_add]
  ring

theorem signedInverseLaplace_sum {ι : Type*} (s : Finset ι) (y : ι → LaurentSeries K) :
    signedInverseLaplace (∑ i ∈ s, y i) = ∑ i ∈ s, signedInverseLaplace (y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, signedInverseLaplace_zero]
  | @insert i s hi ih => simp only [Finset.sum_insert hi, signedInverseLaplace_add, ih]

/-- A typed monomial multiplication coefficient formula, valid at all integer indices. -/
theorem signedLaplace_single_coeff (d : ℤ) (c : K) (y : LaurentSeries K) (m : ℤ) :
    (HahnSeries.single d c * y).coeff m = c * y.coeff (m-d) := by
  conv_lhs => rw [show m = (m-d)+d by omega]
  rw [HahnSeries.coeff_single_mul_add]

theorem signedInverseLaplace_constant (c : K) (y : LaurentSeries K) :
    signedInverseLaplace (HahnSeries.single (0 : ℤ) c * y) =
      PowerSeries.C K c * signedInverseLaplace y := by
  ext n
  rw [signedInverseLaplace_coeff, signedLaplace_single_coeff,
    PowerSeries.coeff_C_mul, signedInverseLaplace_coeff]
  simp only [sub_zero]
  ring

/-- Multiplication by z=w⁻¹ becomes minus ordinary differentiation. -/
theorem signedInverseLaplace_z (y : LaurentSeries K) :
    signedInverseLaplace (HahnSeries.single (-1 : ℤ) (1 : K) * y) =
      -(PowerSeries.derivative K (signedInverseLaplace y)) := by
  ext n
  rw [signedInverseLaplace_coeff, signedLaplace_single_coeff, map_neg,
    PowerSeries.coeff_derivative, signedInverseLaplace_coeff]
  have hn : ((n+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  simp only [one_mul, Nat.cast_add, Nat.cast_one, Nat.factorial_succ, Nat.cast_mul,
    pow_succ]
  have he : (n : ℤ)+1-(-1) = ((n+1 : ℕ) : ℤ)+1 := by omega
  rw [he]
  have hn' : (n : K) + 1 ≠ 0 := by simpa only [Nat.cast_add, Nat.cast_one] using hn
  field_simp [hn', hf]
  <;> ring

/-- The actual D_z=-w²D_w becomes multiplication by the original variable.
The n=0 boundary is killed by the derivative coefficient, with no support premise. -/
theorem signedInverseLaplace_Dz (y : LaurentSeries K) :
    signedInverseLaplace (HahnSeries.single (2 : ℤ) (-1 : K) *
      laurentOrdinaryDerivation y) = PowerSeries.X * signedInverseLaplace y := by
  ext n
  cases n with
  | zero =>
    simp only [signedInverseLaplace_coeff, signedLaplace_single_coeff,
      laurentOrdinaryDerivation_coeff, Nat.cast_zero, zero_add,
      show (1 : ℤ)-2+1=0 by norm_num, Int.cast_zero, zero_mul, mul_zero, zero_div,
      PowerSeries.coeff_zero_X_mul]
  | succ n =>
    rw [signedInverseLaplace_coeff, signedLaplace_single_coeff,
      laurentOrdinaryDerivation_coeff, PowerSeries.coeff_succ_X_mul,
      signedInverseLaplace_coeff]
    have he : ((n+1 : ℕ) : ℤ)+1-2+1 = (n : ℤ)+1 := by omega
    rw [he]
    have hn : ((n+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hf : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
    have hn' : (n : K) + 1 ≠ 0 := by simpa only [Nat.cast_add, Nat.cast_one] using hn
    field_simp [hn', hf]
    <;> ring

theorem signedInverseLaplace_z_iterate (y : LaurentSeries K) (j : ℕ) :
    signedInverseLaplace ((fun x : LaurentSeries K =>
      HahnSeries.single (-1 : ℤ) (1 : K) * x)^[j] y) =
      (fun x : PowerSeries K => -(PowerSeries.derivative K x))^[j]
        (signedInverseLaplace y) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      signedInverseLaplace_z, ih]

theorem signedInverseLaplace_Dz_iterate (y : LaurentSeries K) (i : ℕ) :
    signedInverseLaplace ((fun x : LaurentSeries K =>
      HahnSeries.single (2 : ℤ) (-1 : K) * laurentOrdinaryDerivation x)^[i] y) =
      (fun x : PowerSeries K => PowerSeries.X * x)^[i] (signedInverseLaplace y) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      signedInverseLaplace_Dz, ih]

/-- Signed ordinary Borel input recovers the ORIGINAL factorial coefficients. -/
theorem signedInverseLaplace_signed_input (a : ℕ → K) :
    signedInverseLaplace (HahnSeries.single (1 : ℤ) (1 : K) *
      (HahnSeries.ofPowerSeries ℤ K (PowerSeries.mk fun n => (-1 : K)^n * a n))) =
      PowerSeries.mk (fun n => a n / (n.factorial : K)) := by
  ext n
  rw [signedInverseLaplace_coeff, signedLaplace_single_coeff, PowerSeries.coeff_mk]
  simp only [add_sub_cancel_right, one_mul, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk]
  have hs : (-1 : K)^n * (-1 : K)^n = 1 := by
    rw [← mul_pow]
    simp only [neg_mul_neg, one_mul, one_pow]
  rw [← mul_assoc, hs, one_mul]

theorem signedInverseLaplace_stage41 (a : ℕ → AlgebraicComplex) :
    signedInverseLaplace (HahnSeries.single (1 : ℤ) (1 : AlgebraicComplex) *
      HahnSeries.ofPowerSeries ℤ AlgebraicComplex
        (PowerSeries.mk fun n => (-1 : AlgebraicComplex)^n * a n)) =
      stage41_strictFormalSeries a :=
  signedInverseLaplace_signed_input a

end StrictEUnit
end
