import V5WideSolutionBase
import Mathlib.RingTheory.Derivation.Basic

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Topology
namespace StrictEUnit

/-- A derivative of a literal punctured function, witnessed by a representative
on the plane. No regularity at zero is imposed. -/
def V5HasPuncturedDeriv (r s : V5PuncturedFunctions) : Prop :=
  ∃ g : ℂ → ℂ, (∀ z : ℂˣ, g (z : ℂ) = r z) ∧
    ∀ z : ℂˣ, HasDerivAt g (s z) (z : ℂ)

theorem V5HasPuncturedDeriv.unique {r s t : V5PuncturedFunctions}
    (hs : V5HasPuncturedDeriv r s) (ht : V5HasPuncturedDeriv r t) : s = t := by
  obtain ⟨g, hg, hgs⟩ := hs
  obtain ⟨h, hh, hht⟩ := ht
  funext z
  apply (hgs z).unique
  apply (hht z).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (Units.ne_zero z)] with x hx
  exact (hg (Units.mk0 x hx)).trans (hh (Units.mk0 x hx)).symm

theorem V5HasPuncturedDeriv.const (c : ℂ) :
    V5HasPuncturedDeriv (fun _ => c) 0 :=
  ⟨fun _ => c, fun _ => rfl, fun _ => hasDerivAt_const _ _⟩

theorem V5HasPuncturedDeriv.add {r s u v : V5PuncturedFunctions}
    (hr : V5HasPuncturedDeriv r s) (hu : V5HasPuncturedDeriv u v) :
    V5HasPuncturedDeriv (r + u) (s + v) := by
  obtain ⟨g, hg, hgs⟩ := hr
  obtain ⟨h, hh, hht⟩ := hu
  exact ⟨fun x => g x + h x, fun z => congrArg₂ (· + ·) (hg z) (hh z),
    fun z => (hgs z).add (hht z)⟩

theorem V5HasPuncturedDeriv.mul {r s u v : V5PuncturedFunctions}
    (hr : V5HasPuncturedDeriv r s) (hu : V5HasPuncturedDeriv u v) :
    V5HasPuncturedDeriv (r * u) (s * u + r * v) := by
  obtain ⟨g, hg, hgs⟩ := hr
  obtain ⟨h, hh, hht⟩ := hu
  refine ⟨fun x => g x * h x, fun z => congrArg₂ (· * ·) (hg z) (hh z), ?_⟩
  intro z
  simpa only [hg z, hh z] using (hgs z).mul (hht z)

theorem V5HasPuncturedDeriv.parameter :
    V5HasPuncturedDeriv (fun z : ℂˣ => (z : ℂ)) 1 :=
  ⟨id, fun _ => rfl, fun _ => hasDerivAt_id _⟩

theorem V5HasPuncturedDeriv.inverse_parameter :
    V5HasPuncturedDeriv (fun z : ℂˣ => (↑z⁻¹ : ℂ))
      (fun z => -((↑z⁻¹ : ℂ) * (↑z⁻¹ : ℂ))) := by
  refine ⟨fun x => x⁻¹, fun z => (Units.val_inv_eq_inv_val z).symm, ?_⟩
  intro z
  simpa [Units.val_inv_eq_inv_val, pow_two] using hasDerivAt_inv (Units.ne_zero z)

/-- Stability of the literal generated algebra under complex differentiation.
The hypotheses are exactly a finite Laurent first-order system, not a
fundamental matrix or a prior Picard-Vessiot realization. -/
theorem v5WideSolution_derivative_exists
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))
    (r : v5WideSolutionAlgebra f) :
    ∃ s : v5WideSolutionAlgebra f, V5HasPuncturedDeriv r.val s.val := by
  rcases r with ⟨r, hr⟩
  change r ∈ Algebra.adjoin AlgebraicComplex _ at hr
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩ | ⟨b, rfl⟩
    · let s : v5WideSolutionAlgebra f :=
        ∑ j, v5WideSolutionBase f (A i j) * v5WideSolutionEntry f j
      refine ⟨s, (f i).val, fun _ => rfl, ?_⟩
      intro z
      have he : s.val z = deriv (f i).val (z : ℂ) := by
        change ((v5WideSolutionAlgebra f).val s) z = _
        simp only [s, map_sum, Finset.sum_apply,
          map_mul, Subalgebra.val_apply, Pi.mul_apply, v5WideSolutionEntry,
          v5WideSolutionBase_apply]
        exact (hA z i).symm
      rw [he]
      exact ((f i).property (z : ℂ)).hasDerivAt
    · cases b
      · exact ⟨-(v5WideSolutionParameter f false * v5WideSolutionParameter f false),
          V5HasPuncturedDeriv.inverse_parameter⟩
      · exact ⟨1, V5HasPuncturedDeriv.parameter⟩
  | algebraMap a => exact ⟨0, V5HasPuncturedDeriv.const (a : ℂ)⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s + t, hs.add ht⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨s, hs⟩ := ihx
    obtain ⟨t, ht⟩ := ihy
    exact ⟨s * ⟨y, hy⟩ + ⟨x, hx⟩ * t, hs.mul ht⟩

section Derivation
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι → entireFunctionAlgebra)
    (A : Matrix ι ι (LaurentPolynomial AlgebraicComplex))
    (hA : ∀ z : ℂˣ, ∀ i, deriv (f i).val (z : ℂ) =
      ∑ j, arithmeticLaurentEvaluation z (A i j) * (f j).val (z : ℂ))

/-- The unique derivative in the generated solution algebra. -/
def v5WideSolutionDerivative (r : v5WideSolutionAlgebra f) :
    v5WideSolutionAlgebra f :=
  (v5WideSolution_derivative_exists f A hA r).choose

theorem v5WideSolutionDerivative_spec (r : v5WideSolutionAlgebra f) :
    V5HasPuncturedDeriv r.val (v5WideSolutionDerivative f A hA r).val :=
  (v5WideSolution_derivative_exists f A hA r).choose_spec

theorem v5WideSolutionDerivative_eq (r s : v5WideSolutionAlgebra f)
    (h : V5HasPuncturedDeriv r.val s.val) :
    v5WideSolutionDerivative f A hA r = s :=
  Subtype.ext ((v5WideSolutionDerivative_spec f A hA r).unique h)

/-- Complex differentiation on the actual punctured solution algebra is an
algebraic derivation over the algebraic constants. -/
def v5WideSolutionDerivation : Derivation AlgebraicComplex
    (v5WideSolutionAlgebra f) (v5WideSolutionAlgebra f) where
  toFun := v5WideSolutionDerivative f A hA
  map_add' r s := v5WideSolutionDerivative_eq f A hA _ _
    ((v5WideSolutionDerivative_spec f A hA r).add
      (v5WideSolutionDerivative_spec f A hA s))
  map_smul' c r := by
    apply v5WideSolutionDerivative_eq f A hA
    have h := (V5HasPuncturedDeriv.const (c : ℂ)).mul
      (v5WideSolutionDerivative_spec f A hA r)
    change V5HasPuncturedDeriv
      ((fun _ => (c : ℂ)) * r.val)
      ((fun _ => (c : ℂ)) * (v5WideSolutionDerivative f A hA r).val)
    simpa only [zero_mul, zero_add] using h
  map_one_eq_zero' := v5WideSolutionDerivative_eq f A hA _ _
    (V5HasPuncturedDeriv.const 1)
  leibniz' r s := by
    apply v5WideSolutionDerivative_eq f A hA
    have h := (v5WideSolutionDerivative_spec f A hA r).mul
      (v5WideSolutionDerivative_spec f A hA s)
    change V5HasPuncturedDeriv (r.val * s.val)
      (r.val * (v5WideSolutionDerivative f A hA s).val +
        s.val * (v5WideSolutionDerivative f A hA r).val)
    convert h using 1
    ext z
    change r.val z * _ + s.val z * _ = _ * s.val z + r.val z * _
    ring

@[simp] theorem v5WideSolutionDerivation_coordinate :
    v5WideSolutionDerivation f A hA (v5WideSolutionParameter f true) = 1 :=
  v5WideSolutionDerivative_eq f A hA _ _ V5HasPuncturedDeriv.parameter

@[simp] theorem v5WideSolutionDerivation_inverse_coordinate :
    v5WideSolutionDerivation f A hA (v5WideSolutionParameter f false) =
      -(v5WideSolutionParameter f false * v5WideSolutionParameter f false) :=
  v5WideSolutionDerivative_eq f A hA _ _ V5HasPuncturedDeriv.inverse_parameter

@[simp] theorem v5WideSolutionDerivation_entry (i : ι) :
    v5WideSolutionDerivation f A hA (v5WideSolutionEntry f i) =
      ∑ j, v5WideSolutionBase f (A i j) * v5WideSolutionEntry f j := by
  apply v5WideSolutionDerivative_eq f A hA
  refine ⟨(f i).val, fun _ => rfl, ?_⟩
  intro z
  have he : (↑(∑ j, v5WideSolutionBase f (A i j) *
      v5WideSolutionEntry f j) : V5PuncturedFunctions) z =
      deriv (f i).val (z : ℂ) := by
    change ((v5WideSolutionAlgebra f).val (∑ j, _)) z = _
    simp only [map_sum, Finset.sum_apply, map_mul, Subalgebra.val_apply,
      Pi.mul_apply, v5WideSolutionEntry, v5WideSolutionBase_apply]
    exact (hA z i).symm
  rw [he]
  exact ((f i).property (z : ℂ)).hasDerivAt

end Derivation

end StrictEUnit
#print axioms StrictEUnit.V5HasPuncturedDeriv.unique

#print axioms StrictEUnit.v5WideSolution_derivative_exists
#print axioms StrictEUnit.v5WideSolutionDerivation

#print axioms StrictEUnit.v5WideSolutionDerivation_entry
