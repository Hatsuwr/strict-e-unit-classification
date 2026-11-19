import V5WideRelationLiftingEndpoint
import PolynomialRelationFiber
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit

/-- Literal functions on the punctured complex line. -/
abbrev V5PuncturedFunctions := ℂˣ → ℂ

def v5WideSolutionAlgebra {ι : Type} (f : ι → entireFunctionAlgebra) :
    Subalgebra AlgebraicComplex V5PuncturedFunctions :=
  Algebra.adjoin AlgebraicComplex
    (Set.range (fun i => fun z : ℂˣ => (f i).val (z : ℂ)) ∪
      Set.range (fun b : Bool => fun z : ℂˣ => if b then (z : ℂ) else (↑z⁻¹ : ℂ)))

def v5WideSolutionEntry {ι : Type} (f : ι → entireFunctionAlgebra) (i : ι) :
    v5WideSolutionAlgebra f :=
  ⟨fun z => (f i).val (z : ℂ), Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)⟩

def v5WideSolutionParameter {ι : Type} (f : ι → entireFunctionAlgebra) (b : Bool) :
    v5WideSolutionAlgebra f :=
  ⟨fun z => if b then (z : ℂ) else (↑z⁻¹ : ℂ),
    Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩)⟩

def v5WideSolutionEvaluation {ι : Type} (f : ι → entireFunctionAlgebra) :
    v5WideSolutionAlgebra f →ₐ[AlgebraicComplex] ℂ where
  toFun r := r.val 1
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

def v5WideSolutionIdeal {ι : Type} (f : ι → entireFunctionAlgebra) :
    Ideal (v5WideSolutionAlgebra f) :=
  Ideal.span {v5WideSolutionParameter f true - 1}

private theorem v5WideSolution_generates {ι : Type} (f : ι → entireFunctionAlgebra) :
    Algebra.adjoin AlgebraicComplex
      (Set.range (v5WideSolutionEntry f) ∪ Set.range (v5WideSolutionParameter f)) = ⊤ := by
  apply top_unique
  intro r hrTop
  clear hrTop
  rcases r with ⟨r, hr⟩
  change r ∈ Algebra.adjoin AlgebraicComplex _ at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩
    · exact Algebra.subset_adjoin (Or.inl ⟨i, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩)
  | algebraMap a => exact Subalgebra.algebraMap_mem _ a
  | add x y hx hy ihx ihy => exact Subalgebra.add_mem _ ihx ihy
  | mul x y hx hy ihx ihy => exact Subalgebra.mul_mem _ ihx ihy

private theorem v5WideSolution_parameter_mem {ι : Type}
    (f : ι → entireFunctionAlgebra) (b : Bool) :
    ∃ a : AlgebraicComplex, v5WideSolutionParameter f b - algebraMap _ _ a ∈
      v5WideSolutionIdeal f := by
  refine ⟨1, ?_⟩
  rw [map_one]
  have hz : v5WideSolutionParameter f true - 1 ∈ v5WideSolutionIdeal f :=
    Ideal.subset_span (Set.mem_singleton _)
  cases b
  · have he : v5WideSolutionParameter f false - 1 =
        -(v5WideSolutionParameter f false * (v5WideSolutionParameter f true - 1)) := by
      apply Subtype.ext
      funext z
      change (↑z⁻¹ : ℂ) - 1 = -((↑z⁻¹ : ℂ) * ((z : ℂ) - 1))
      rw [mul_sub, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
      ring
    rw [he]
    exact (v5WideSolutionIdeal f).neg_mem ((v5WideSolutionIdeal f).mul_mem_left _ hz)
  · exact hz

private def v5PuncturedEval (z : ℂˣ) :
    V5PuncturedFunctions →ₐ[AlgebraicComplex] ℂ where
  toFun r := r z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

private theorem v5_map_polynomial_mv_eval
    {k A C ι : Type*} [CommRing k] [CommRing A] [CommRing C]
    [Algebra k A] [Algebra k C] (φ : A →ₐ[k] C) (f : ι → A)
    (x : A) (Q : Polynomial (MvPolynomial ι k)) :
    φ (Polynomial.eval₂ (MvPolynomial.aeval f).toRingHom x Q) =
      Polynomial.eval₂ (MvPolynomial.aeval (fun i => φ (f i))).toRingHom (φ x) Q := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.eval₂_add, map_add, hP, hQ]
  | monomial j a =>
    simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
    congr 1
    exact MvPolynomial.comp_aeval_apply f φ a

/-- The algebraic specialization ideal is exactly the kernel of literal numerical
 evaluation. The proof uses the checked wide Laurent-system lifting theorem. -/
theorem v5WideSolution_exact_kernel
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ)) :
    RingHom.ker (v5WideSolutionEvaluation f).toRingHom = v5WideSolutionIdeal f := by
  apply kernel_eq_of_generated_polynomial_lifts
    (v5WideSolutionEvaluation f) (v5WideSolutionEntry f) (v5WideSolutionParameter f)
    (v5WideSolutionParameter f true) (v5WideSolutionIdeal f)
    (v5WideSolution_generates f) (v5WideSolution_parameter_mem f)
  · apply Ideal.span_le.mpr
    rintro x (rfl : x = _)
    change (1 : ℂ) - 1 = 0
    ring
  · exact Ideal.subset_span (Set.mem_singleton _)
  · intro P hP
    have hP' : MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
        (fun i => (f i).val 1) P = 0 := by
      rw [MvPolynomial.comp_aeval_apply] at hP
      exact hP
    obtain ⟨Q, hQ, hQP⟩ := v5_actual_wide_laurent_lifting ι f A hf hA P hP'
    refine ⟨Q, ?_, hQP⟩
    apply Subtype.ext
    funext z
    let φ := (v5PuncturedEval z).comp (v5WideSolutionAlgebra f).val
    exact (v5_map_polynomial_mv_eval φ (v5WideSolutionEntry f)
      (v5WideSolutionParameter f true) Q).trans (hQ z)


/-- The actual fiber S/(z-1)S, not a replacement by its reduced numerical image. -/
abbrev V5WideSolutionFiber {ι : Type} (f : ι → entireFunctionAlgebra) :=
  (v5WideSolutionAlgebra f) ⧸ v5WideSolutionIdeal f

section ExactFiber
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hf : ∀ i, V5IsBroadEFunction (f i).val)
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

/-- Numerical evaluation descends to the full chosen algebraic fiber. -/
def v5WideSolutionFiberEvaluation : V5WideSolutionFiber f →ₐ[AlgebraicComplex] ℂ :=
  Ideal.Quotient.liftₐ (v5WideSolutionIdeal f) (v5WideSolutionEvaluation f)
    (fun _ hr => RingHom.mem_ker.mp ((v5WideSolution_exact_kernel f A hf hA).ge hr))

theorem v5WideSolutionFiberEvaluation_injective :
    Function.Injective (v5WideSolutionFiberEvaluation f A hf hA) := by
  apply RingHom.lift_injective_of_ker_le_ideal
  exact le_of_eq (v5WideSolution_exact_kernel f A hf hA)

@[simp] theorem v5WideSolutionFiberEvaluation_entry (i : ι) :
    v5WideSolutionFiberEvaluation f A hf hA
      (Ideal.Quotient.mk (v5WideSolutionIdeal f) (v5WideSolutionEntry f i)) =
        (f i).val 1 := rfl

include A hf hA in
/-- A literal numerical reciprocal pair gives inverse classes in the full fiber. -/
theorem v5WideSolutionFiber_reciprocal (i j : ι)
    (hij : (f i).val 1 * (f j).val 1 = 1) :
    Ideal.Quotient.mk (v5WideSolutionIdeal f) (v5WideSolutionEntry f i) *
      Ideal.Quotient.mk (v5WideSolutionIdeal f) (v5WideSolutionEntry f j) = 1 := by
  apply v5WideSolutionFiberEvaluation_injective f A hf hA
  simpa using hij

/-- The chosen first entry is a genuine unit in S/(z-1)S. This does not assert
it is already a unit in S, which is a separate descent problem. -/
def v5WideSolutionFiberUnit (i j : ι)
    (hij : (f i).val 1 * (f j).val 1 = 1) : (V5WideSolutionFiber f)ˣ where
  val := Ideal.Quotient.mk (v5WideSolutionIdeal f) (v5WideSolutionEntry f i)
  inv := Ideal.Quotient.mk (v5WideSolutionIdeal f) (v5WideSolutionEntry f j)
  val_inv := v5WideSolutionFiber_reciprocal f A hf hA i j hij
  inv_val := v5WideSolutionFiber_reciprocal f A hf hA j i (by simpa [mul_comm] using hij)

end ExactFiber

end StrictEUnit
#print axioms StrictEUnit.v5WideSolution_exact_kernel

#print axioms StrictEUnit.v5WideSolutionFiberEvaluation_injective
#print axioms StrictEUnit.v5WideSolutionFiberUnit
