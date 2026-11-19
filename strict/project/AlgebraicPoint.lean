import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraic points of nonzero finite-type algebras

This is the weak-Nullstellensatz step used in Section 9. Existence of an
algebraic point is proved, not supplied as an input: choose a maximal ideal,
apply Zariski's lemma to its residue field, then use algebraic closedness.

The resulting homomorphism is an abstract k-point. It is not the original
embedding of a numerical value algebra into the complex numbers. We do not
instantiate the finite-type algebra with the manuscript's unconstructed
numerical fiber here, and do not construct a torsor chart from this point.
-/

noncomputable section
namespace StrictEUnit

variable {k S : Type*} [Field k] [IsAlgClosed k] [CommRing S]
  [Algebra k S] [Algebra.FiniteType k S]

/-- Every maximal residue field of a finite-type algebra over an
algebraically closed field is isomorphic to the base field as a k-algebra. -/
def maximalResidueEquiv (m : Ideal S) [m.IsMaximal] : k ≃ₐ[k] S ⧸ m := by
  letI := Ideal.Quotient.field m
  letI : Module.Finite k (S ⧸ m) :=
    finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  exact AlgEquiv.ofBijective (Algebra.ofId k (S ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- An actual k-valued algebra homomorphism associated with a maximal ideal. -/
def maximalIdealPoint (m : Ideal S) [m.IsMaximal] : S →ₐ[k] k :=
  (maximalResidueEquiv (k := k) m).symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m)

/-- The point has precisely the chosen maximal ideal as its kernel. -/
theorem maximalIdealPoint_ker (m : Ideal S) [m.IsMaximal] :
    RingHom.ker (maximalIdealPoint (k := k) m).toRingHom = m := by
  ext s
  change (maximalResidueEquiv (k := k) m).symm (Ideal.Quotient.mk m s) = 0 ↔ s ∈ m
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (maximalResidueEquiv (k := k) m).symm.injective
    simpa only [map_zero] using h
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- A nontrivial finite-type algebra over an algebraically closed field has
an algebraic point. This is an existence conclusion, not a point hypothesis. -/
theorem nonempty_algebraic_point [Nontrivial S] : Nonempty (S →ₐ[k] k) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : m.IsMaximal := hm
  exact ⟨maximalIdealPoint (k := k) m⟩

/-- A version recording both the point and its maximal kernel. -/
theorem exists_algebraic_point_with_maximal_kernel [Nontrivial S] :
    ∃ p : S →ₐ[k] k, (RingHom.ker p.toRingHom).IsMaximal := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : m.IsMaximal := hm
  refine ⟨maximalIdealPoint (k := k) m, ?_⟩
  rw [maximalIdealPoint_ker]
  exact hm

end StrictEUnit

#print axioms StrictEUnit.maximalResidueEquiv
#print axioms StrictEUnit.maximalIdealPoint
#print axioms StrictEUnit.maximalIdealPoint_ker
#print axioms StrictEUnit.nonempty_algebraic_point
#print axioms StrictEUnit.exists_algebraic_point_with_maximal_kernel
