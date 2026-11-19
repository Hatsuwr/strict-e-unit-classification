import FiniteDimensionalRationalRatio
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Uniform rational-ratio degree bound for one fixed finite family

No finite-dimensionality of the ambient extension is assumed. The proof
uses only the finite K(z)-span of the given family. This is a field-linear
infrastructure result, not the stable-subspace bound or the Type-II rank theorem.
-/

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- For a fixed finite S in an extension L/K(z), any ratio lying in K(z)
between elements of span_K(S) has polynomial numerator and nonzero denominator
of uniformly bounded degrees. The bound is chosen before a, b and q. -/
theorem exists_uniform_finite_family_rational_ratio_bound
    {K L I : Type*} [Field K] [Field L]
    [Algebra K L] [Algebra (RatFunc K) L]
    [IsScalarTower K (RatFunc K) L] [Fintype I] (S : I → L) :
    ∃ D : ℕ, ∀ a b : L,
      a ∈ Submodule.span K (Set.range S) →
      b ∈ Submodule.span K (Set.range S) → b ≠ 0 →
      ∀ q : RatFunc K, a = algebraMap (RatFunc K) L q * b →
      ∃ p₁ p₂ : Polynomial K, p₂ ≠ 0 ∧
        p₁.natDegree ≤ D ∧ p₂.natDegree ≤ D ∧
        q = algebraMap (Polynomial K) (RatFunc K) p₁ /
          algebraMap (Polynomial K) (RatFunc K) p₂ := by
  classical
  let E : Submodule (RatFunc K) L := Submodule.span (RatFunc K) (Set.range S)
  letI : FiniteDimensional (RatFunc K) E :=
    FiniteDimensional.span_of_finite (RatFunc K) (Set.finite_range S)
  let S' : I → E := fun i => ⟨S i, Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨D, hD⟩ := exists_uniform_finiteDimensional_rational_ratio_bound (K := K) S'
  have hcoe (w : I → K) :
      (((∑ i, algebraMap K (RatFunc K) (w i) • S' i) : E) : L) =
        ∑ i, w i • S i := by
    rw [Submodule.coe_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change algebraMap K (RatFunc K) (w i) • S i = w i • S i
    exact IsScalarTower.algebraMap_smul (RatFunc K) (w i) (S i)
  refine ⟨D, ?_⟩
  intro a b ha hb hbne q hab
  obtain ⟨α, hα⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp ha
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hb
  have hb' : (∑ i, algebraMap K (RatFunc K) (β i) • S' i) ≠ 0 := by
    intro hz
    apply hbne
    have hc := congrArg (fun x : E => (x : L)) hz
    simpa only [hcoe, Submodule.coe_zero, hβ] using hc
  have hab' :
      (∑ i, algebraMap K (RatFunc K) (α i) • S' i) =
        q • (∑ i, algebraMap K (RatFunc K) (β i) • S' i) := by
    apply Subtype.ext
    rw [Submodule.coe_smul, hcoe, hcoe, hα, hβ]
    simpa only [Algebra.smul_def] using hab
  exact hD α β q hb' hab'

end StrictEUnit
end
