import RelativeClosedPolynomial
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! New reconstruction, not recovered historical source.
Relative algebraic closure over a perfect field implies disjointness from
algebraic extensions, first for finite subfields, then by finite reduction. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit

/-- A finite subfield of a common overfield is linearly disjoint from a
relatively algebraically closed extension of the perfect ground field. -/
theorem relative_closed_linearDisjoint_finite
    {F E Ω : Type*} [Field F] [Field E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω]
    [PerfectField F] [IsIntegrallyClosedIn F E]
    (A : IntermediateField F Ω) [FiniteDimensional F A] :
    A.LinearDisjoint E := by
  let pb : PowerBasis F A := Field.powerBasisOfFiniteOfSeparable F A
  have hm : minpoly E (A.val pb.gen) =
      (minpoly F pb.gen).map (algebraMap F E) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
      (relative_closed_monic_irreducible_map (minpoly.monic pb.isIntegral_gen)
        (minpoly.irreducible pb.isIntegral_gen))
    · rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algHom_apply,
        minpoly.aeval, map_zero]
    · exact (minpoly.monic pb.isIntegral_gen).map _
  have hd : (minpoly E (A.val pb.gen)).natDegree = pb.dim := by
    rw [hm, Polynomial.natDegree_map, pb.natDegree_minpoly]
  let e : Fin pb.dim → Fin (minpoly E (A.val pb.gen)).natDegree := fun i =>
    ⟨i.val, by simpa only [hd] using i.isLt⟩
  have he : Function.Injective e := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun a : Fin (minpoly E (A.val pb.gen)).natDegree => a.val) hij
  have hp : LinearIndependent E
      (fun i : Fin pb.dim => (A.val pb.gen) ^ (i : ℕ)) :=
    (linearIndependent_pow (K := E) (A.val pb.gen)).comp e he
  apply IntermediateField.LinearDisjoint.of_basis_left pb.basis
  have hfun : A.val ∘ pb.basis =
      (fun i : Fin pb.dim => (A.val pb.gen) ^ (i : ℕ)) := by
    funext i
    change A.val (pb.basis i) = (A.val pb.gen) ^ (i : ℕ)
    rw [pb.basis_eq_pow, map_pow]
  rw [hfun]
  exact hp

/-- Any algebraic field extension is linearly disjoint from an extension in
which the perfect ground field is relatively algebraically closed. -/
theorem relative_closed_tensor_isDomain_algebraic
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [PerfectField F] [IsIntegrallyClosedIn F E]
    (K : Type*) [Field K] [Algebra F K] [Algebra.IsAlgebraic F K] :
    IsDomain (E ⊗[F] K) := by
  let Ω := AlgebraicClosure E
  let j : K →ₐ[F] Ω := IsAlgClosed.lift
  let A : IntermediateField F Ω := j.fieldRange
  letI : Algebra.IsIntegral F A.toSubalgebra :=
    Algebra.IsIntegral.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  have hdis : A.LinearDisjoint E := by
    apply Subalgebra.LinearDisjoint.of_linearDisjoint_finite_left
    intro A' _ hfin
    let Afield : IntermediateField F Ω := Algebra.IsAlgebraic.toIntermediateField A'
    letI : FiniteDimensional F Afield := hfin
    exact relative_closed_linearDisjoint_finite Afield
  have hdis' : (IsScalarTower.toAlgHom F E Ω).fieldRange.LinearDisjoint j.fieldRange := by
    apply IntermediateField.linearDisjoint_iff'.mpr
    exact Subalgebra.LinearDisjoint.symm hdis
  exact IntermediateField.LinearDisjoint.isDomain' hdis'

end StrictEUnit
