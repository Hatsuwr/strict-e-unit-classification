import V5ArithmeticLaurentEval
import V5ActualArithmeticMeromorphic
import V5BroadActualData
import V5KummerUnitAnalytic

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 120000
attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
open scoped TensorProduct
namespace StrictEUnit

/-- If left-factor pullbacks have arithmetic entire pole-clearing numerators,
the literal Kummer tensor realization has that property at every element.
The scalar coefficients of its normalized units are then algebraic. -/
theorem v5_arithmetic_kummer_tensor_unit {ι : Type} (f : ι → entireFunctionAlgebra)
    {D : Type*} [CommRing D] [Algebra V5LaurentBase D]
    (q : ℕ) (ω : D →+* V5LaurentBase)
    (hω : ∀ p, ω (algebraMap V5LaurentBase D p) = v5LaurentPower q p)
    (hS : ∀ s : v5WideSolutionAlgebra f, V5ArithmeticMeromorphicZero
      (algebraicClosure ℚ ℂ).toSubfield (fun z => s.val (z^q))) :
    ∃ η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex,
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z = s.val (z^q) *
        arithmeticLaurentEvaluation z (ω d)) ∧
      (∀ (u : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D), IsUnit u →
        ∃ (m : ℤ) (W : entireFunctionAlgebra), (∀ z, W.val z ≠ 0) ∧
          (∀ z : ℂˣ, (η u).val z = (z : ℂ)^m * W.val z) ∧
          (η u).val 1 = W.val 1 ∧ W.val 0 ∈ (algebraicClosure ℚ ℂ).toSubfield) := by
  obtain ⟨η, hη, _⟩ := v5_actual_kummer_punctured_realization f q ω hω
  refine ⟨η,hη,?_⟩
  let k := (algebraicClosure ℚ ℂ).toSubfield
  have hA (x : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D) :
      V5ArithmeticMeromorphicZero k (η x).val := by
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [η.map_zero]
      exact V5ArithmeticMeromorphicZero.const k 0
    | tmul s d =>
      have he : (η (s ⊗ₜ[V5LaurentBase] d)).val =
          (fun z => s.val (z^q)) * (fun z => arithmeticLaurentEvaluation z (ω d)) :=
        funext (hη s d)
      rw [he]
      exact (hS s).mul (v5_arithmetic_laurent_eval k (ω d))
    | add x y hx hy =>
      rw [η.map_add]
      exact hx.add hy
  intro u hu
  obtain ⟨m,W,hW,hWnz,hrep,hmark⟩ := v5_meromorphic_unit_normalization (η u) (hu.map η)
  let W' : entireFunctionAlgebra := ⟨W,hW⟩
  exact ⟨m,W',hWnz,hrep,hmark,v5_arithmetic_normalized_value (hA u) W' hrep⟩


/-- Every genuine broad E-function supplies the original algebraic Taylor
coefficients needed by the arithmetic Kummer tensor normalization. -/
theorem v5_broad_mem_arithmetic_entire (f : entireFunctionAlgebra)
    (hf : V5IsBroadEFunction f.val) :
    f ∈ subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield := by
  obtain ⟨a, _, hs, _, _⟩ := hf
  apply (mem_subfieldEntireFunctionAlgebra _ _).mpr
  intro n
  have hcoeff : entireCauchyCoefficient f.val n = (a n : ℂ)/(n.factorial : ℂ) := by
    apply entireCauchyCoefficient_eq_of_hasSum f.property
    intro z
    convert hs z using 1
    funext j
    ring
  rw [hcoeff]
  exact Subfield.div_mem _ (a n).property (natCast_mem _ _)

/-- Arithmetic normalized units on the actual Kummer cover of broad
E-generators. The only new scalar extension input is the marked Laurent base. -/
theorem v5_actual_wide_kummer_tensor_unit {ι : Type} (f : ι → entireFunctionAlgebra)
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    {D : Type*} [CommRing D] [Algebra V5LaurentBase D]
    (q : ℕ) (hq : 0 < q) (ω : D →+* V5LaurentBase)
    (hω : ∀ p, ω (algebraMap V5LaurentBase D p) = v5LaurentPower q p) :
    ∃ η : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D →+*
        v5MeromorphicZeroAlgebra AlgebraicComplex,
      (∀ s d z, (η (s ⊗ₜ[V5LaurentBase] d)).val z = s.val (z^q) *
        arithmeticLaurentEvaluation z (ω d)) ∧
      (∀ (u : v5WideSolutionAlgebra f ⊗[V5LaurentBase] D), IsUnit u →
        ∃ (m : ℤ) (W : entireFunctionAlgebra), (∀ z, W.val z ≠ 0) ∧
          (∀ z : ℂˣ, (η u).val z = (z : ℂ)^m * W.val z) ∧
          (η u).val 1 = W.val 1 ∧ W.val 0 ∈ (algebraicClosure ℚ ℂ).toSubfield) :=
  v5_arithmetic_kummer_tensor_unit f q ω hω fun s =>
    v5_wide_solution_arithmetic_meromorphic_pullback f
      (fun i => v5_broad_mem_arithmetic_entire (f i) (hf i)) s hq

end StrictEUnit
#print axioms StrictEUnit.v5_arithmetic_kummer_tensor_unit
#print axioms StrictEUnit.v5_broad_mem_arithmetic_entire
#print axioms StrictEUnit.v5_actual_wide_kummer_tensor_unit
