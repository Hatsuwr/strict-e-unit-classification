import MinimalPrefixRemainder
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! NEW SOURCE-ONLY. Coefficientwise extension of a Laurent-series family from
K to L preserves rational-function linear independence. The proof uses K-linear
coordinate functionals on L, never treats them as multiplicative, and does not
assume that arbitrary scalar extension preserves an arbitrary module embedding.
No finite extension, Galois, characteristic-zero or analytic premise is needed. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Apply a K-linear functional to each polynomial coefficient. This is not a
ring map and is never used as one. -/
def coefficientLinearPolynomial (ell : L →ₗ[K] K) (p : Polynomial L) : Polynomial K :=
  Polynomial.ofFinsupp (p.toFinsupp.mapRange ell (map_zero ell))

@[simp] theorem coefficientLinearPolynomial_coeff (ell : L →ₗ[K] K)
    (p : Polynomial L) (n : ℕ) :
    (coefficientLinearPolynomial ell p).coeff n = ell (p.coeff n) := rfl

/-- The coefficientwise additive map on Laurent series. Well-ordered support
is preserved because a zero-preserving map can only shrink it. -/
def coefficientLinearLaurent (ell : L →ₗ[K] K) : LaurentSeries L →+ LaurentSeries K where
  toFun x := x.map ell
  map_zero' := by ext n; simp
  map_add' := by intro x y; ext n; simp

/-- The linear map pulls out K-valued coefficients on the right. This is the
specific scalar compatibility needed, not multiplicativity on L. -/
theorem coefficientLinearLaurent_mul (ell : L →ₗ[K] K)
    (x : LaurentSeries L) (y : LaurentSeries K) :
    coefficientLinearLaurent ell (x * y.map (algebraMap K L)) =
      coefficientLinearLaurent ell x * y := by
  have hmul (a : L) (b : K) : ell (a * algebraMap K L b) = ell a * b := by
    rw [mul_comm a]
    rw [← Algebra.smul_def]
    rw [map_smul]
    simp only [smul_eq_mul, mul_comm b]
  ext n
  change ell ((x * y.map (algebraMap K L)).coeff n) =
    (x.map ell * y).coeff n
  simp only [HahnSeries.coeff_mul, map_sum, HahnSeries.map_coeff, hmul]
  refine Eq.symm (Finset.sum_subset (fun ij hij => ?_) (fun ij hij hnot => ?_))
  · simp only [Finset.mem_addAntidiagonal, HahnSeries.mem_support,
      HahnSeries.map_coeff] at hij ⊢
    refine ⟨?_, ?_, hij.2.2⟩
    · intro hx
      exact hij.1 (by rw [hx, map_zero])
    · intro hy
      apply hij.2.1
      apply (algebraMap K L).injective
      simpa only [map_zero] using hy
  · simp only [Finset.mem_addAntidiagonal, HahnSeries.mem_support,
      HahnSeries.map_coeff] at hij hnot
    by_cases hx : ell (x.coeff ij.1) = 0
    · simp only [hx, zero_mul]
    · have hy : y.coeff ij.2 ≠ 0 := by
        intro h
        exact hij.2.1 (by rw [h, map_zero])
      exact False.elim (hnot ⟨hx, hy, hij.2.2⟩)

/-- Coefficient extraction agrees exactly with the canonical polynomial
embedding into Laurent series, including all negative indices. -/
theorem coefficientLinearLaurent_polynomial (ell : L →ₗ[K] K) (p : Polynomial L) :
    coefficientLinearLaurent ell (algebraMap (Polynomial L) (LaurentSeries L) p) =
      algebraMap (Polynomial K) (LaurentSeries K) (coefficientLinearPolynomial ell p) := by
  ext n
  change ell ((algebraMap (Polynomial L) (LaurentSeries L) p).coeff n) =
    (algebraMap (Polynomial K) (LaurentSeries K) (coefficientLinearPolynomial ell p)).coeff n
  simp only [Polynomial.algebraMap_hahnSeries_apply, PowerSeries.coeff_coe,
    Polynomial.coeff_coe, coefficientLinearPolynomial_coeff, apply_ite, map_zero]
  by_cases hn : n < 0 <;> simp [hn]

/-- Any polynomial relation over L descends coefficientwise through every
K-linear coordinate functional. Original K(z)-independence forces all its
L-polynomial coefficients to vanish. -/
theorem laurent_polynomial_relation_baseChange_zero {r : ℕ}
    (Y : Fin r → LaurentSeries K) (hY : LinearIndependent (RatFunc K) Y)
    (P : Fin r → Polynomial L)
    (hrel : (∑ i, algebraMap (Polynomial L) (LaurentSeries L) (P i) *
      (Y i).map (algebraMap K L)) = 0) : ∀ i, P i = 0 := by
  intro i
  apply Polynomial.ext
  intro n
  apply (Module.forall_dual_apply_eq_zero_iff K ((P i).coeff n)).mp
  intro ell
  have hK : (∑ j, algebraMap (Polynomial K) (LaurentSeries K)
      (coefficientLinearPolynomial ell (P j)) * Y j) = 0 := by
    have h := congrArg (coefficientLinearLaurent ell) hrel
    simpa only [map_sum, map_zero, coefficientLinearLaurent_mul,
      coefficientLinearLaurent_polynomial] using h
  have hi : coefficientLinearPolynomial ell (P i) = 0 := by
    by_contra hne
    exact polynomial_row_remainder_ne_zero Y hY
      (fun j => coefficientLinearPolynomial ell (P j)) ⟨i, hne⟩ hK
  have hc := congrArg (fun p : Polynomial K => p.coeff n) hi
  simpa only [coefficientLinearPolynomial_coeff, Polynomial.coeff_zero] using hc

/-- Exact coefficientwise Laurent base change preserves rational-function
independence. Finite L(z) denominators are cleared first; the preceding theorem
then applies K-linear coefficient functionals, with no analytic hypothesis. -/
theorem laurent_rational_linearIndependent_baseChange {r : ℕ}
    (Y : Fin r → LaurentSeries K) (hY : LinearIndependent (RatFunc K) Y) :
    LinearIndependent (RatFunc L) (fun i => (Y i).map (algebraMap K L)) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  obtain ⟨T, hT⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (Polynomial L)) c
  choose P hP using hT
  have hTne : algebraMap (Polynomial L) (RatFunc L) (T : Polynomial L) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors T.property
  have hpoly : (∑ j, algebraMap (Polynomial L) (LaurentSeries L) (P j) *
      (Y j).map (algebraMap K L)) = 0 := by
    calc
      _ = ∑ j, algebraMap (Polynomial L) (RatFunc L) (P j) •
          (Y j).map (algebraMap K L) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply
          (Polynomial L) (RatFunc L) (LaurentSeries L)]
      _ = algebraMap (Polynomial L) (RatFunc L) (T : Polynomial L) •
          (∑ j, c j • (Y j).map (algebraMap K L)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hP j, Algebra.smul_def (T : Polynomial L) (c j), mul_smul]
      _ = 0 := by rw [hc, smul_zero]
  have hPzero := laurent_polynomial_relation_baseChange_zero Y hY P hpoly
  have hz : algebraMap (Polynomial L) (RatFunc L) (T : Polynomial L) * c i = 0 := by
    rw [← Algebra.smul_def, ← hP i, hPzero i, map_zero]
  exact (mul_eq_zero.mp hz).resolve_left hTne

end StrictEUnit
end
