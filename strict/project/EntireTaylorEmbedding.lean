import AnalyticFormalTaylor
import Mathlib.RingTheory.Adjoin.Basic

/-!
The entire-function algebra and its genuine Taylor embedding. The carrier is
actual functions on the whole complex plane, and injectivity is proved using
the global Cauchy reconstruction theorem, not assumed as a realization axiom.
-/
noncomputable section
namespace StrictEUnit

/-- The subalgebra of actual entire complex functions, with pointwise operations. -/
def entireFunctionAlgebra : Subalgebra ℂ (ℂ → ℂ) where
  carrier := {f | Differentiable ℂ f}
  zero_mem' := differentiable_const 0
  one_mem' := differentiable_const 1
  add_mem' := fun hf hg => hf.add hg
  mul_mem' := fun hf hg => hf.mul hg
  algebraMap_mem' := fun c => differentiable_const c

@[simp] theorem mem_entireFunctionAlgebra (f : ℂ → ℂ) :
    f ∈ entireFunctionAlgebra ↔ Differentiable ℂ f := Iff.rfl

lemma entireFormalTaylor_add {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g) :
    entireFormalTaylor (fun z => f z + g z) = entireFormalTaylor f + entireFormalTaylor g := by
  ext n
  simp only [coeff_entireFormalTaylor, map_add]
  apply entireCauchyCoefficient_eq_of_hasSum (hf.add hg)
  intro z
  simpa only [add_mul] using
    (entireCauchyCoefficient_hasSum hf z).add (entireCauchyCoefficient_hasSum hg z)

@[simp] lemma entireFormalTaylor_const (c : ℂ) :
    entireFormalTaylor (fun _ => c) = PowerSeries.C ℂ c := by
  simpa using entireFormalTaylor_polynomial (Polynomial.C c)

/-- Equality of the genuine Taylor series of two entire functions is equality
of the actual functions at every complex point. -/
theorem entireFormalTaylor_injective_on_entire {f g : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (h : entireFormalTaylor f = entireFormalTaylor g) : f = g := by
  have hc : entireCauchyCoefficient f = entireCauchyCoefficient g := by
    funext n
    simpa only [coeff_entireFormalTaylor] using congrArg (PowerSeries.coeff ℂ n) h
  funext z
  exact (entireCauchyCoefficient_hasSum hf z).unique
    (by simpa only [hc] using entireCauchyCoefficient_hasSum hg z)

/-- A concrete complex-algebra homomorphism from entire functions to formal series. -/
def entireTaylorAlgHom : entireFunctionAlgebra →ₐ[ℂ] PowerSeries ℂ where
  toFun f := entireFormalTaylor f.val
  map_zero' := by
    change entireFormalTaylor (fun _ => 0) = 0
    rw [entireFormalTaylor_const, map_zero]
  map_one' := by
    change entireFormalTaylor (fun _ => 1) = 1
    rw [entireFormalTaylor_const, map_one]
  map_add' f g := entireFormalTaylor_add f.property g.property
  map_mul' f g := entireFormalTaylor_mul f.property g.property
  commutes' c := entireFormalTaylor_const c

@[simp] theorem entireTaylorAlgHom_apply (f : entireFunctionAlgebra) :
    entireTaylorAlgHom f = entireFormalTaylor f.val := rfl

@[simp] theorem coeff_entireTaylorAlgHom (f : entireFunctionAlgebra) (n : ℕ) :
    PowerSeries.coeff ℂ n (entireTaylorAlgHom f) = entireCauchyCoefficient f.val n := by
  simp

theorem entireTaylorAlgHom_injective : Function.Injective entireTaylorAlgHom := by
  intro f g h
  apply Subtype.ext
  exact entireFormalTaylor_injective_on_entire f.property g.property h

/-- This equivalence is only with the image of entire functions, not with all
formal power series. No convergence claim is made for arbitrary series. -/
def entireTaylorImageEquiv : entireFunctionAlgebra ≃ₐ[ℂ] entireTaylorAlgHom.range :=
  AlgEquiv.ofInjective entireTaylorAlgHom entireTaylorAlgHom_injective

/-- Evaluation remains evaluation of an actual entire function at a complex point. -/
def entireEvaluation (z : ℂ) : entireFunctionAlgebra →ₐ[ℂ] ℂ where
  toFun f := f.val z
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem entireEvaluation_apply (z : ℂ) (f : entireFunctionAlgebra) :
    entireEvaluation z f = f.val z := rfl

/-- A unit in the actual entire-function ring has no zeros. -/
theorem entireFunction_unit_nonzero (f : entireFunctionAlgebra) (hf : IsUnit f)
    (z : ℂ) : f.val z ≠ 0 :=
  (hf.map (entireEvaluation z)).ne_zero

/-- Differentiation stays within the actual entire-function algebra. -/
def entireFunctionDerivative (f : entireFunctionAlgebra) : entireFunctionAlgebra :=
  ⟨deriv f.val, differentiableOn_univ.mp (f.property.differentiableOn.deriv isOpen_univ)⟩

@[simp] theorem entireTaylorAlgHom_derivative (f : entireFunctionAlgebra) :
    entireTaylorAlgHom (entireFunctionDerivative f) =
      PowerSeries.derivative ℂ (entireTaylorAlgHom f) :=
  entireFormalTaylor_deriv f.property

/-- Polynomials are embedded as their actual evaluation functions. -/
def polynomialEntireAlgHom : Polynomial ℂ →ₐ[ℂ] entireFunctionAlgebra where
  toFun P := ⟨fun z => P.eval z, P.differentiable⟩
  map_zero' := by ext z; simp
  map_one' := by ext z; simp
  map_add' P Q := by ext z; simp
  map_mul' P Q := by ext z; simp
  commutes' c := by ext z; simp

@[simp] theorem polynomialEntireAlgHom_apply (P : Polynomial ℂ) (z : ℂ) :
    (polynomialEntireAlgHom P).val z = P.eval z := rfl

/-- The analytic-to-formal map agrees exactly with the existing polynomial inclusion. -/
@[simp] theorem entireTaylorAlgHom_polynomial (P : Polynomial ℂ) :
    entireTaylorAlgHom (polynomialEntireAlgHom P) = (P : PowerSeries ℂ) :=
  entireFormalTaylor_polynomial P

/-- The Taylor image of an actually generated entire-function algebra is the
algebra generated by the actual Taylor series of its generators. -/
theorem entireTaylorAlgHom_adjoin (s : Set entireFunctionAlgebra) :
    (Algebra.adjoin ℂ s).map entireTaylorAlgHom =
      Algebra.adjoin ℂ (entireTaylorAlgHom '' s) :=
  (Algebra.adjoin_image ℂ entireTaylorAlgHom s).symm

/-- Taylor equality does not lose polynomial relations among entire functions. -/
theorem entireTaylorAlgHom_polynomial_relation (P : Polynomial ℂ)
    (f : entireFunctionAlgebra) :
    Polynomial.aeval f P = 0 ↔ Polynomial.aeval (entireTaylorAlgHom f) P = 0 := by
  rw [Polynomial.aeval_algHom_apply entireTaylorAlgHom f P]
  exact ⟨fun h => by rw [h, map_zero],
    fun h => entireTaylorAlgHom_injective (h.trans (map_zero entireTaylorAlgHom).symm)⟩

/-- Entrywise Taylor expansion of an actual matrix of entire functions. -/
def entireTaylorMatrix {m n : Type*} (F : Matrix m n entireFunctionAlgebra) :
    Matrix m n (PowerSeries ℂ) := F.map entireTaylorAlgHom

theorem entireTaylorMatrix_injective (m n : Type*) :
    Function.Injective (@entireTaylorMatrix m n) :=
  Matrix.map_injective entireTaylorAlgHom_injective

/-- Determinants commute with the actual analytic Taylor embedding. -/
theorem entireTaylorMatrix_det {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n entireFunctionAlgebra) :
    entireTaylorAlgHom F.det = (entireTaylorMatrix F).det :=
  RingHom.map_det entireTaylorAlgHom.toRingHom F

/-- A supplied entire inverse determinant maps to a genuine formal inverse
identity. Such an entire inverse is not asserted to exist for arbitrary F. -/
theorem entireTaylorMatrix_det_inverse {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n entireFunctionAlgebra) (g : entireFunctionAlgebra)
    (hg : F.det * g = 1) :
    (entireTaylorMatrix F).det * entireTaylorAlgHom g = 1 := by
  rw [← entireTaylorMatrix_det, ← map_mul, hg, map_one]

/-- The actual complex derivative, bundled as a derivation of entire functions. -/
def entireFunctionDerivation : Derivation ℂ entireFunctionAlgebra entireFunctionAlgebra where
  toFun := entireFunctionDerivative
  map_add' f g := by
    apply Subtype.ext
    funext z
    exact deriv_add (f.property z) (g.property z)
  map_smul' c f := by
    apply Subtype.ext
    funext z
    exact deriv_const_mul c (f.property z)
  map_one_eq_zero' := by
    apply Subtype.ext
    funext z
    exact deriv_const z 1
  leibniz' f g := by
    apply Subtype.ext
    funext z
    change deriv (fun w => f.val w * g.val w) z =
      f.val z * deriv g.val z + g.val z * deriv f.val z
    rw [deriv_mul (f.property z) (g.property z)]
    ring

@[simp] theorem entireFunctionDerivation_apply (f : entireFunctionAlgebra) (z : ℂ) :
    (entireFunctionDerivation f).val z = deriv f.val z := rfl

/-- The actual identity coordinate, an entire function on the complex plane. -/
def entireCoordinate : entireFunctionAlgebra := ⟨fun z => z, differentiable_id⟩

@[simp] theorem entireCoordinate_apply (z : ℂ) : entireCoordinate.val z = z := rfl

@[simp] theorem entireFunctionDerivation_coordinate :
    entireFunctionDerivation entireCoordinate = 1 := by
  apply Subtype.ext
  funext z
  exact deriv_id z

@[simp] theorem entireTaylorAlgHom_coordinate :
    entireTaylorAlgHom entireCoordinate = PowerSeries.X := by
  simpa [entireCoordinate, polynomialEntireAlgHom] using
    entireTaylorAlgHom_polynomial (Polynomial.X : Polynomial ℂ)

@[simp] theorem entireTaylorAlgHom_derivation (f : entireFunctionAlgebra) :
    entireTaylorAlgHom (entireFunctionDerivation f) =
      PowerSeries.derivative ℂ (entireTaylorAlgHom f) :=
  entireTaylorAlgHom_derivative f

end StrictEUnit
