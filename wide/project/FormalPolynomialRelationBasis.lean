import PolynomialRelationSplitting
import OrdinaryBorelLaurentRelation

/-! The split relation-basis theorem applied to literal formal Laurent families.
Its target torsion-freeness is proved from the injective polynomial inclusion. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
variable {K ι : Type*} [Field K] [Fintype ι]

def formalPolynomialRelationMap (f : ι → LaurentSeries K) :
    (ι → Polynomial K) →ₗ[Polynomial K] LaurentSeries K :=
  Fintype.linearCombination (Polynomial K) f

/-- One basis of actual formal polynomial relations retains rank at every
specialization. It need not exhaust numerical relations at that point. -/
theorem formalPolynomialRelation_specialization_basis (f : ι → LaurentSeries K) :
    ∃ r : ℕ, ∃ b : Basis (Fin r) (Polynomial K)
        (LinearMap.ker (formalPolynomialRelationMap f)),
      ∀ a : K, LinearIndependent K (fun i j => ((b i).val j).eval a) := by
  letI : NoZeroSMulDivisors (Polynomial K) (LaurentSeries K) :=
    NoZeroSMulDivisors.iff_algebraMap_injective.mpr
      (Polynomial.algebraMap_hahnSeries_injective ℤ)
  exact polynomialRelationKernel_specialization_basis (formalPolynomialRelationMap f)
end StrictEUnit
