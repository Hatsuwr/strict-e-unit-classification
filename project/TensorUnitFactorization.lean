import UniversalRankOneIdeal
import TensorUnitScalarProducts
import FiniteAlgebraImageScalars

/-! Product-unit factorization over an algebraically closed field. The
universal finite coefficient algebra is mapped to the actual right-hand
algebra, and coefficient scalarity is derived from its proved finiteness.
Neither factorization nor the finite-module conclusion is a hypothesis. -/
noncomputable section
open scoped TensorProduct BigOperators
open MvPolynomial
namespace StrictEUnit
variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B]

/-- Evaluation at the actual pairwise products of expansion coefficients. -/
def coefficientProductEvaluation {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) :
    MvPolynomial (Fin d.size × Fin e.size) k →ₐ[k] B :=
  MvPolynomial.aeval (fun ij => d.right ij.1 * e.right ij.2)

/-- The actual inverse-pair equations kill every defining relation of the
universal affine coefficient algebra. -/
theorem coefficientProductEvaluation_kills_ideal {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) (hxy : x * y = 1)
    {Γ : Type*} (basis : Basis Γ k A) :
    Ideal.map dehomogenize.toRingHom (universalRankOneIdeal basis d.left e.left) ≤
      RingHom.ker (coefficientProductEvaluation d e).toRingHom := by
  classical
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro p (⟨q, rfl⟩ | ⟨γ, rfl⟩)
  · change coefficientProductEvaluation d e
      (dehomogenize (universalRankOneMinor q.1.1 q.1.2 q.2.1 q.2.2)) = 0
    simpa [coefficientProductEvaluation, universalRankOneMinor, dehomogenize,
      sub_eq_zero] using
      coefficient_products_minors d.right e.right q.1.1 q.1.2 q.2.1 q.2.2
  · change coefficientProductEvaluation d e
      (dehomogenize (universalProductCoordinate basis d.left e.left γ)) = 0
    simpa [coefficientProductEvaluation, universalProductCoordinate, dehomogenize,
      sub_eq_zero, Algebra.smul_def] using d.product_coordinate_relation e hxy basis γ

/-- The proved-finite universal quotient has an actual algebra map to B. -/
def coefficientProductQuotientEvaluation {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) (hxy : x * y = 1)
    {Γ : Type*} (basis : Basis Γ k A) :
    (MvPolynomial (Fin d.size × Fin e.size) k ⧸
      Ideal.map dehomogenize.toRingHom (universalRankOneIdeal basis d.left e.left)) →ₐ[k] B :=
  Ideal.Quotient.liftₐ _ (coefficientProductEvaluation d e)
    (fun _ hp => coefficientProductEvaluation_kills_ideal d e hxy basis hp)

/-- Images of the universal coordinate classes are the genuine coefficient products. -/
theorem coefficientProductQuotientEvaluation_X {x y : A ⊗[k] B}
    (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y) (hxy : x * y = 1)
    {Γ : Type*} (basis : Basis Γ k A) (i : Fin d.size) (j : Fin e.size) :
    coefficientProductQuotientEvaluation d e hxy basis
      (Ideal.Quotient.mkₐ k _ (X (i, j))) = d.right i * e.right j := by
  simp [coefficientProductQuotientEvaluation, coefficientProductEvaluation]

/-- Scalarity is derived from the finite universal algebra and an actual map,
not assumed for the tensor coefficients. No finite-type hypothesis is needed. -/
theorem inverse_pair_coefficient_products_scalar [IsAlgClosed k] [IsDomain A] [IsDomain B]
    {x y : A ⊗[k] B} (d : FiniteTensorExpansion x) (e : FiniteTensorExpansion y)
    (hxy : x * y = 1) (i : Fin d.size) (j : Fin e.size) :
    ∃ c : k, algebraMap k B c = d.right i * e.right j := by
  let basis := Basis.ofVectorSpace k A
  letI := universalRankOneIdeal_finite basis d.left e.left d.independent e.independent
  obtain ⟨c, hc⟩ := finite_algebra_hom_image_scalar
    (coefficientProductQuotientEvaluation d e hxy basis)
    (Ideal.Quotient.mkₐ k _ (X (i, j)))
  exact ⟨c, hc.trans (coefficientProductQuotientEvaluation_X d e hxy basis i j)⟩

/-- Every actual tensor-product unit over an algebraically closed field is a
pure tensor when both factors are domains. No geometric or factorization
hypothesis, finite-type assumption, or supplied coefficient-scalar premise remains. -/
theorem tensor_unit_is_pure [IsAlgClosed k] [IsDomain A] [IsDomain B]
    (u : (A ⊗[k] B)ˣ) :
    ∃ a : A, ∃ b : B, (u : A ⊗[k] B) = a ⊗ₜ[k] b := by
  apply unit_pure_of_scalar_coefficient_products u
  exact inverse_pair_coefficient_products_scalar
    (finiteTensorExpansion (u : A ⊗[k] B))
    (finiteTensorExpansion (↑u⁻¹ : A ⊗[k] B)) (by simp)

end StrictEUnit
#print axioms StrictEUnit.coefficientProductEvaluation
#print axioms StrictEUnit.coefficientProductEvaluation_kills_ideal
#print axioms StrictEUnit.coefficientProductQuotientEvaluation
#print axioms StrictEUnit.coefficientProductQuotientEvaluation_X
#print axioms StrictEUnit.inverse_pair_coefficient_products_scalar
#print axioms StrictEUnit.tensor_unit_is_pure
