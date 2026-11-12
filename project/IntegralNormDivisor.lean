import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Source-only non-Galois norm divisor. A finite integral basis and Cramer's
identity produce an integral quotient of the integer norm by the element.
No absolute-norm size bound or polynomial denominator theorem is asserted. -/
noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

/-- Adjugation supplies the norm quotient in any finite free commutative algebra. -/
theorem exists_mul_eq_algebraNorm_of_basis
    {R S I : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Fintype I] [DecidableEq I] (B : Basis I R S) (x : S) :
    ∃ y : S, x * y = algebraMap R S (Algebra.norm R x) := by
  let M := Algebra.leftMulMatrix B x
  let w : I → R := M.cramer (fun i => B.repr (1 : S) i)
  let y : S := B.equivFun.symm w
  have hy : (fun i => B.repr y i) = w := B.equivFun.apply_symm_apply w
  have hc : (fun i => B.repr (x * y) i) =
      (Algebra.norm R x) • (fun i => B.repr (1 : S) i) := by
    calc
      (fun i => B.repr (x * y) i) = M *ᵥ (fun i => B.repr y i) :=
        (Algebra.leftMulMatrix_mulVec_repr B x y).symm
      _ = M *ᵥ w := by rw [hy]
      _ = M.det • (fun i => B.repr (1 : S) i) := Matrix.mulVec_cramer M _
      _ = (Algebra.norm R x) • (fun i => B.repr (1 : S) i) := by
        rw [Algebra.norm_eq_matrix_det B x]
  have heq : x * y = (Algebra.norm R x) • (1 : S) := by
    apply B.ext_elem
    intro i
    simpa only [map_smul, Finsupp.smul_apply, Pi.smul_apply] using congrFun hc i
  exact ⟨y, by simpa only [Algebra.smul_def, mul_one] using heq⟩

/-- No IsGalois hypothesis: the element divides its literal integer norm. -/
theorem ringOfIntegers_dvd_integer_norm
    {K : Type*} [Field K] [NumberField K] (v : 𝓞 K) :
    v ∣ (Algebra.norm ℤ v : 𝓞 K) := by
  classical
  obtain ⟨b, hb⟩ := exists_mul_eq_algebraNorm_of_basis (NumberField.RingOfIntegers.basis K) v
  exact ⟨b, hb.symm⟩

/-- The same nonzero signed integer is identified with the rational field norm.
Absolute value and House estimates are separate later obligations. -/
theorem exists_nonzero_integer_norm_divisor
    {K : Type*} [Field K] [NumberField K] (v : 𝓞 K) (hv : v ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : ℚ) = Algebra.norm ℚ (v : K) ∧ v ∣ (n : 𝓞 K) := by
  refine ⟨Algebra.norm ℤ v, Algebra.norm_ne_zero_iff.mpr hv,
    Algebra.coe_norm_int v, ringOfIntegers_dvd_integer_norm v⟩

end StrictEUnit
end
