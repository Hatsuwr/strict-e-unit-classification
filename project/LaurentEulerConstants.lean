import Mathlib.RingTheory.LaurentSeries

/-! Coefficient and constant-kernel facts for the actual Laurent-series Euler
operator. This does not establish a derivation on a logarithmic extension. -/
noncomputable section
namespace StrictEUnit
open HahnSeries
variable {k : Type*} [Field k]

/-- The actual operator t d/dt, with t the Laurent monomial of degree one. -/
def laurentEuler (f : LaurentSeries k) : LaurentSeries k :=
  single (1:ℤ) (1:k) * LaurentSeries.derivative k f

@[simp] theorem laurentEuler_coeff (f : LaurentSeries k) (n : ℤ) :
    (laurentEuler f).coeff n = (n:k) * f.coeff n := by
  unfold laurentEuler
  rw [show n = (n - 1) + 1 by omega, coeff_single_mul_add]
  simp [LaurentSeries.hasseDeriv_coeff, zsmul_eq_mul]

@[simp] theorem laurentEuler_coeff_zero (f : LaurentSeries k) :
    (laurentEuler f).coeff 0 = 0 := by simp

/-- In characteristic zero, the kernel consists exactly of constant series. -/
theorem laurentEuler_eq_zero_iff [CharZero k] (f : LaurentSeries k) :
    laurentEuler f = 0 ↔ f = single (0:ℤ) (f.coeff 0) := by
  constructor
  · intro hf
    ext n
    by_cases hn : n = 0
    · subst n; simp
    · have hc := congrArg (fun g : LaurentSeries k => g.coeff n) hf
      have hn' : (n:k) ≠ 0 := by exact_mod_cast hn
      have hz : f.coeff n = 0 := by
        simpa only [laurentEuler_coeff, coeff_zero, mul_eq_zero, hn', false_or] using hc
      simp [hn, hz]
  · intro hf
    ext n
    rw [laurentEuler_coeff]
    by_cases hn : n = 0
    · subst n; simp
    · have hc := congrArg (fun g : LaurentSeries k => g.coeff n) hf
      have hz : f.coeff n = 0 := by simpa [hn] using hc
      simp [hz]

/-- A nonzero constant cannot be an Euler derivative, in any characteristic. -/
theorem laurentEuler_ne_nonzero_constant (f : LaurentSeries k) (c : k) (hc : c ≠ 0) :
    laurentEuler f ≠ single (0:ℤ) c := by
  intro h
  have hz := congrArg (fun g : LaurentSeries k => g.coeff 0) h
  apply hc
  simpa using hz.symm

#print axioms laurentEuler
#print axioms laurentEuler_coeff
#print axioms laurentEuler_coeff_zero
#print axioms laurentEuler_eq_zero_iff
#print axioms laurentEuler_ne_nonzero_constant
end StrictEUnit
