import FrobeniusResonanceCoefficientUniqueness
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.BigOperators

/-!
# An unconditional finite-dimensional bound for the formal solution space

The solution space consists of ALL polynomial-valued coefficient sequences
satisfying the actual Frobenius convolution. It is not defined as the span of
constructed solutions. A concrete finite coefficient map is proved injective;
finite dimensionality and the indicial-degree bound follow, rather than being
assumed. Surjectivity or a spanning theorem is not asserted here.
-/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- All formal polynomial-log coefficient solutions of the literal equation. -/
def polynomialLogFormalSolutionSpace (B : ℕ → Polynomial K) (rho : K) :
    Submodule K (ℕ → Polynomial K) where
  carrier := {u | ∀ n,polynomialLogEulerCoefficient B rho u n = 0}
  zero_mem' := by
    intro n
    simp only [polynomialLogEulerCoefficient,Pi.zero_apply,map_zero,Finset.sum_const_zero]
  add_mem' := by
    intro u v hu hv n
    rw [polynomialLogEulerCoefficient_add,hu n,hv n,add_zero]
  smul_mem' := by
    intro c u hu n
    rw [polynomialLogEulerCoefficient_smul,hu n,smul_zero]

variable [CharZero K]

/-- Exactly the low-log coefficients at actual resonant natural indices. -/
def polynomialLogResonanceCoordinateIndex (rho : K) (P : Polynomial K) :=
  Σ n : {n : ℕ // n ∈ polynomialResonanceIndices rho P},
    Fin (polynomialResonanceMultiplicity rho P n.1)

instance polynomialLogResonanceCoordinateIndexFintype (rho : K) (P : Polynomial K) :
    Fintype (polynomialLogResonanceCoordinateIndex rho P) := by
  unfold polynomialLogResonanceCoordinateIndex
  infer_instance

theorem polynomialLogResonanceCoordinateIndex_card (rho : K) (P : Polynomial K) :
    Fintype.card (polynomialLogResonanceCoordinateIndex rho P) =
      polynomialResonanceTotalCost rho P := by
  simp only [polynomialLogResonanceCoordinateIndex,Fintype.card_sigma,Fintype.card_fin]
  exact Finset.sum_coe_sort (polynomialResonanceIndices rho P)
    (polynomialResonanceMultiplicity rho P)

/-- Literal coefficient extraction on the full solution space. -/
def polynomialLogResonanceCoordinates (B : ℕ → Polynomial K) (rho : K) :
    polynomialLogFormalSolutionSpace B rho →ₗ[K]
      (polynomialLogResonanceCoordinateIndex rho (B 0) → K) where
  toFun u i := (u.1 i.1.1).coeff i.2.1
  map_add' u v := by
    funext i
    exact Polynomial.coeff_add _ _ _
  map_smul' c u := by
    funext i
    exact Polynomial.coeff_smul _ _ _

theorem polynomialLogResonanceCoordinates_injective
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0) :
    Function.Injective (polynomialLogResonanceCoordinates B rho) := by
  intro u v huv
  apply Subtype.ext
  apply polynomialLogSolution_unique_of_resonance_coefficients B rho hP u.1 v.1 u.2 v.2
  intro n j hj
  have hmem : n ∈ polynomialResonanceIndices rho (B 0) :=
    (polynomialResonanceIndices_mem rho (B 0) n).mpr
      (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le j) hj))
  exact congrFun huv ⟨⟨n,hmem⟩,⟨j,hj⟩⟩

/-- Finite dimensionality is derived from actual equation/coefficients, not
supplied as a hypothesis or built into the definition of the solution space. -/
theorem polynomialLogFormalSolutionSpace_finiteDimensional
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0) :
    FiniteDimensional K (polynomialLogFormalSolutionSpace B rho) :=
  FiniteDimensional.of_injective (polynomialLogResonanceCoordinates B rho)
    (polynomialLogResonanceCoordinates_injective B rho hP)

/-- The sharper bound counts only resonant indices in this nonnegative tail. -/
theorem polynomialLogFormalSolutionSpace_finrank_le_resonanceCost
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0) :
    Module.finrank K (polynomialLogFormalSolutionSpace B rho) ≤
      polynomialResonanceTotalCost rho (B 0) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (polynomialLogResonanceCoordinates_injective B rho hP)
  simpa only [Module.finrank_fintype_fun_eq_card,
    polynomialLogResonanceCoordinateIndex_card] using h

/-- No algebraic closure or splitting hypothesis is needed for the degree
bound on ALL formal coefficient solutions. -/
theorem polynomialLogFormalSolutionSpace_finrank_le_indicial_degree
    (B : ℕ → Polynomial K) (rho : K) (hP : B 0 ≠ 0) :
    Module.finrank K (polynomialLogFormalSolutionSpace B rho) ≤ (B 0).natDegree :=
  (polynomialLogFormalSolutionSpace_finrank_le_resonanceCost B rho hP).trans
    (polynomialResonanceTotalCost_le rho (B 0))

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogResonanceCoordinateIndex_card
#print axioms StrictEUnit.polynomialLogResonanceCoordinates_injective
#print axioms StrictEUnit.polynomialLogFormalSolutionSpace_finiteDimensional
#print axioms StrictEUnit.polynomialLogFormalSolutionSpace_finrank_le_resonanceCost
#print axioms StrictEUnit.polynomialLogFormalSolutionSpace_finrank_le_indicial_degree
