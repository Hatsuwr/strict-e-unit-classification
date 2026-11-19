import V5MeromorphicTensor
import V5WideSolutionRelativeBase

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
open scoped TensorProduct
namespace StrictEUnit

theorem v5_wide_solution_meromorphic_zero {ι : Type} (f : ι → entireFunctionAlgebra)
    (s : v5WideSolutionAlgebra f) : V5MeromorphicZero s.val := by
  rcases s with ⟨s, hs⟩
  change s ∈ Algebra.adjoin AlgebraicComplex _ at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i,rfl⟩ | ⟨b,rfl⟩
    · exact V5MeromorphicZero.of_entire (f i).property
    · cases b
      · exact V5MeromorphicZero.invCoord
      · exact V5MeromorphicZero.of_entire differentiable_id
  | algebraMap a => exact V5MeromorphicZero.of_entire (differentiable_const (a : ℂ))
  | add x y hx hy ihx ihy => exact ihx.add ihy
  | mul x y hx hy ihx ihy => exact ihx.mul ihy

def v5WideSolutionToMeromorphic {ι : Type} (f : ι → entireFunctionAlgebra) :
    v5WideSolutionAlgebra f →ₐ[AlgebraicComplex] v5MeromorphicZeroAlgebra AlgebraicComplex :=
  (v5WideSolutionAlgebra f).val.codRestrict _ (v5_wide_solution_meromorphic_zero f)

theorem v5WideSolutionToMeromorphic_base {ι : Type} (f : ι → entireFunctionAlgebra)
    (p : V5LaurentBase) :
    v5WideSolutionToMeromorphic f (v5WideSolutionBase f p) =
      v5MeromorphicZeroLaurent AlgebraicComplex p := by
  apply Subtype.ext
  funext z
  change (v5WideSolutionBase f p).val z = _
  rw [v5WideSolutionBase_apply, v5MeromorphicZeroLaurent_apply]
  rfl

/-- The actual Kummer-extended solution algebra maps to literal punctured
functions with at worst a pole at zero. Ring identities, including unit
identities, are preserved, as is the tensor mark. No injectivity claim. -/
theorem v5_actual_kummer_punctured_realization {ι : Type} (f : ι → entireFunctionAlgebra)
    {D : Type*} [CommRing D] [Algebra V5LaurentBase D]
    (q : ℕ) (ω : D →+* V5LaurentBase)
    (hω : ∀ p, ω (algebraMap V5LaurentBase D p) = v5LaurentPower q p) :
    ∃ η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex,
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z = s.val (z^q) *
        arithmeticLaurentEvaluation z (ω d)) ∧
      (∀ s d, (η (s ⊗ₜ[V5LaurentBase] d)).val 1 =
        s.val 1 * arithmeticLaurentEvaluation 1 (ω d)) := by
  exact v5_kummer_meromorphic_tensor q (v5WideSolutionToMeromorphic f).toRingHom ω
    (v5WideSolutionToMeromorphic_base f) hω

end StrictEUnit
#print axioms StrictEUnit.v5_wide_solution_meromorphic_zero
#print axioms StrictEUnit.v5WideSolutionToMeromorphic_base
#print axioms StrictEUnit.v5_actual_kummer_punctured_realization
