import ArithmeticRecovery
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Arithmetic recovery from a genuine formal logarithmic derivative equation.
The Taylor-series realization and the equation for an analytic unit remain
separate: this file does not assume derivative coefficients are already in k. -/
noncomputable section
namespace StrictEUnit
variable {L : Type*} [Field L] (k : Subfield L)

theorem powerSeries_coeff_mem_mul (f g : PowerSeries L)
    (hf : ∀ n, PowerSeries.coeff L n f ∈ k)
    (hg : ∀ n, PowerSeries.coeff L n g ∈ k) :
    ∀ n, PowerSeries.coeff L n (f * g) ∈ k := by
  intro n
  rw [PowerSeries.coeff_mul]
  apply k.sum_mem
  intro ij _
  exact k.mul_mem (hf ij.1) (hg ij.2)

theorem powerSeries_coeff_mem_inv (f : PowerSeries L)
    (hf : ∀ n, PowerSeries.coeff L n f ∈ k) :
    ∀ n, PowerSeries.coeff L n f⁻¹ ∈ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [PowerSeries.coeff_inv]
    have hc : PowerSeries.constantCoeff L f ∈ k := by
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hf 0
    split_ifs with hn
    · exact k.inv_mem hc
    · apply k.mul_mem (k.neg_mem (k.inv_mem hc))
      apply k.sum_mem
      intro ij _
      split_ifs with hij
      · exact k.mul_mem (hf ij.1) (ih ij.2 hij)
      · exact k.zero_mem

theorem powerSeries_coeff_mem_derivative (f : PowerSeries L)
    (hf : ∀ n, PowerSeries.coeff L n f ∈ k) :
    ∀ n, PowerSeries.coeff L n (PowerSeries.derivative L f) ∈ k := by
  intro n
  rw [PowerSeries.coeff_derivative]
  exact k.mul_mem (hf (n+1)) (by simpa only [Nat.cast_add, Nat.cast_one] using natCast_mem k (n+1))

theorem phase_derivative_coeff_mem_of_formal_equation (P : Polynomial L)
    (f : PowerSeries L) (hf : ∀ n, PowerSeries.coeff L n f ∈ k)
    (hf0 : PowerSeries.constantCoeff L f ≠ 0)
    (hode : PowerSeries.derivative L f = (P.derivative : PowerSeries L) * f) :
    ∀ n, P.derivative.coeff n ∈ k := by
  have hquot : (P.derivative : PowerSeries L) = PowerSeries.derivative L f * f⁻¹ := by
    rw [hode, mul_assoc, PowerSeries.mul_inv_cancel f hf0, mul_one]
  intro n
  have hc := powerSeries_coeff_mem_mul k (PowerSeries.derivative L f) f⁻¹
    (powerSeries_coeff_mem_derivative k f hf) (powerSeries_coeff_mem_inv k f hf) n
  rw [← hquot] at hc
  simpa only [Polynomial.coeff_coe] using hc

theorem phase_over_subfield_of_formal_equation [CharZero L] (P : Polynomial L)
    (hP0 : P.coeff 0 = 0) (f : PowerSeries L)
    (hf : ∀ n, PowerSeries.coeff L n f ∈ k)
    (hf0 : PowerSeries.constantCoeff L f ≠ 0)
    (hode : PowerSeries.derivative L f = (P.derivative : PowerSeries L) * f) :
    ∃ Q : Polynomial k, Q.map k.subtype = P := by
  exact exists_subfield_polynomial_of_derivative k P (by simpa [hP0] using k.zero_mem)
    (phase_derivative_coeff_mem_of_formal_equation k P f hf hf0 hode)
end StrictEUnit
#print axioms StrictEUnit.powerSeries_coeff_mem_mul
#print axioms StrictEUnit.powerSeries_coeff_mem_inv
#print axioms StrictEUnit.powerSeries_coeff_mem_derivative
#print axioms StrictEUnit.phase_derivative_coeff_mem_of_formal_equation
#print axioms StrictEUnit.phase_over_subfield_of_formal_equation
