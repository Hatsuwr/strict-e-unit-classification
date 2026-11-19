import PolynomialIntegralCommonNorm
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-! Source-only: the adjugate step for ONE matrix shared by an arbitrary family.
This does not construct that matrix or prove its rank. All H entries are
polynomials, not rational functions with unremoved poles. -/
noncomputable section
open scoped NumberField
namespace StrictEUnit

/-- Right multiplication by one mapped matrix can be cleared by its determinant,
with the exact mapped integral numerator supplied by the adjugate. -/
theorem common_matrix_adjugate_entry
    {R S : Type*} [CommRing R] [CommRing S] {n : Type*}
    [Fintype n] [DecidableEq n] (φ : R →+* S)
    (M B : Matrix n n R) (H : Matrix n n S)
    (h : H * φ.mapMatrix M = φ.mapMatrix B) (i j : n) :
    φ M.det * H i j = φ ((B * M.adjugate) i j) := by
  have he : φ.mapMatrix (B * M.adjugate) = (φ.mapMatrix M).det • H := by
    rw [map_mul, φ.map_adjugate, ← h, Matrix.mul_assoc,
      Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]
  have hij := congrArg (fun A : Matrix n n S => A i j) he
  change φ ((B * M.adjugate) i j) = (φ.mapMatrix M).det * H i j at hij
  rw [← φ.map_det] at hij
  exact hij.symm

/-- One fixed nonzero coefficient of the SAME determinant supplies one integer
denominator for every coefficient of every matrix in an arbitrary family.
The hypothesis H_l * map M = map B_l must be established by the actual
differential construction separately; no such construction is assumed hidden. -/
theorem common_matrix_coefficient_norm_clears_family
    {K I : Type*} [Field K] [NumberField K] (r : ℕ)
    (M : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (H : I → Matrix (Fin r) (Fin r) (Polynomial K))
    (B : I → Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (h : ∀ l : I, H l *
      (Polynomial.mapRingHom (algebraMap (𝓞 K) K)).mapMatrix M =
        (Polynomial.mapRingHom (algebraMap (𝓞 K) K)).mapMatrix (B l))
    (k : ℕ) (hk : M.det.coeff k ≠ 0) :
    Algebra.norm ℤ (M.det.coeff k) ≠ 0 ∧
      (Algebra.norm ℤ (M.det.coeff k) : ℚ) =
        Algebra.norm ℚ ((M.det.coeff k : 𝓞 K) : K) ∧
      ∀ l : I, ∀ i j : Fin r, ∀ d : ℕ,
        IsIntegral ℤ ((Algebra.norm ℤ (M.det.coeff k) : K) * (H l i j).coeff d) := by
  let φ : Polynomial (𝓞 K) →+* Polynomial K :=
    Polynomial.mapRingHom (algebraMap (𝓞 K) K)
  have hprod (x : I × Fin r × Fin r) (d : ℕ) :
      IsIntegral ℤ ((M.det.map (algebraMap (𝓞 K) K) * H x.1 x.2.1 x.2.2).coeff d) := by
    have he := common_matrix_adjugate_entry φ M (B x.1) (H x.1)
      (h x.1) x.2.1 x.2.2
    change IsIntegral ℤ ((φ M.det * H x.1 x.2.1 x.2.2).coeff d)
    rw [he]
    change IsIntegral ℤ ((((B x.1 * M.adjugate) x.2.1 x.2.2).map (algebraMap (𝓞 K) K)).coeff d)
    rw [Polynomial.coeff_map]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  obtain ⟨hne, hnorm, hclear⟩ := polynomial_common_coefficient_norm_clears_family
    M.det k hk (fun x : I × Fin r × Fin r => H x.1 x.2.1 x.2.2) hprod
  exact ⟨hne, hnorm, fun l i j d => hclear (l, i, j) d⟩

end StrictEUnit
end
