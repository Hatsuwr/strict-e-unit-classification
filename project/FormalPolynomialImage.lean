import AlgebraicInterfaces
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Adjoin.Basic

/-! Actual polynomial subalgebras of a rational-function field. The variable is
formal; no analytic realization of any coefficient or logarithm is asserted. -/
noncomputable section
namespace StrictEUnit
variable {k L : Type*} [Field k] [Field L] [Algebra k L]

def formalPolynomialEmbedding (S : Subalgebra k L) : Polynomial S →ₐ[k] RatFunc L :=
  (IsScalarTower.toAlgHom k (Polynomial L) (RatFunc L)).comp (Polynomial.mapAlgHom S.val)

theorem formalPolynomialEmbedding_injective (S : Subalgebra k L) :
    Function.Injective (formalPolynomialEmbedding S) :=
  (IsFractionRing.injective (Polynomial L) (RatFunc L)).comp
    (Polynomial.map_injective S.val.toRingHom Subtype.val_injective)

@[simp] theorem formalPolynomialEmbedding_C (S : Subalgebra k L) (s : S) :
    formalPolynomialEmbedding S (Polynomial.C s) = RatFunc.C (s : L) := by
  change algebraMap (Polynomial L) (RatFunc L) ((Polynomial.C s).map S.val.toRingHom) = _
  simp

@[simp] theorem formalPolynomialEmbedding_X (S : Subalgebra k L) :
    formalPolynomialEmbedding S Polynomial.X = RatFunc.X := by
  change algebraMap (Polynomial L) (RatFunc L) (Polynomial.X.map S.val.toRingHom) = _
  simp

def formalPolynomialImageEquiv (S : Subalgebra k L) :
    Polynomial S ≃ₐ[k] (formalPolynomialEmbedding S).range :=
  AlgEquiv.ofInjective _ (formalPolynomialEmbedding_injective S)

theorem formalPolynomialEmbedding_range (S : Subalgebra k L) :
    (formalPolynomialEmbedding S).range =
      Algebra.adjoin k (insert RatFunc.X (RatFunc.C '' (S : Set L))) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    change formalPolynomialEmbedding S p ∈ _
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [map_add] using Subalgebra.add_mem _ hp hq
    | monomial n s =>
      rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
        formalPolynomialEmbedding_C, formalPolynomialEmbedding_X]
      exact Subalgebra.mul_mem _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨s, s.property, rfl⟩))
        (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_insert _ _)) n)
  · rw [Algebra.adjoin_le_iff]
    rintro x (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨Polynomial.X, formalPolynomialEmbedding_X S⟩
    · exact ⟨Polynomial.C ⟨s, hs⟩, formalPolynomialEmbedding_C S ⟨s, hs⟩⟩

theorem formalPolynomialImage_unit_is_coefficient (S : Subalgebra k L)
    (u : (formalPolynomialEmbedding S).range) (hu : IsUnit u) :
    ∃ s : S, IsUnit s ∧ RatFunc.C (s : L) = (u : RatFunc L) := by
  let e := formalPolynomialImageEquiv S
  obtain ⟨s, hs, hp⟩ := polynomial_unit_is_constant (e.symm u) (hu.map e.symm.toRingHom)
  refine ⟨s, hs, ?_⟩
  have h := congrArg (fun p => ((e p : (formalPolynomialEmbedding S).range) : RatFunc L)) hp
  dsimp only at h
  rw [e.apply_symm_apply] at h
  exact (formalPolynomialEmbedding_C S s).symm.trans h

end StrictEUnit
#print axioms StrictEUnit.formalPolynomialEmbedding
#print axioms StrictEUnit.formalPolynomialEmbedding_injective
#print axioms StrictEUnit.formalPolynomialEmbedding_C
#print axioms StrictEUnit.formalPolynomialEmbedding_X
#print axioms StrictEUnit.formalPolynomialImageEquiv
#print axioms StrictEUnit.formalPolynomialEmbedding_range
#print axioms StrictEUnit.formalPolynomialImage_unit_is_coefficient
