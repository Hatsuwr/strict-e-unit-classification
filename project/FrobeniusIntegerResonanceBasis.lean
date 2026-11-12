import FrobeniusIntegerResonanceSpanning

/-! The fixed all-integer family is an actual Basis of the full Laurent
solution space. Dimension and unique expansions follow, including empty index. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def integerResonanceFrobeniusSolution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    polynomialLogLaurentSolutionSpace r b ξ :=
  ⟨integerResonanceFrobeniusCoefficients _ ξ i,
    integerResonanceFrobeniusCoefficients_solution r b ξ hP i⟩

theorem integerResonanceFrobeniusSolution_linearIndependent
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    LinearIndependent K (integerResonanceFrobeniusSolution r b ξ hP) :=
  LinearIndependent.of_comp (polynomialLogLaurentSolutionSpace r b ξ).subtype
    (integerResonanceFrobeniusCoefficients_linearIndependent _ ξ)

theorem integerResonanceFrobeniusSolution_span_eq_top
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Submodule.span K (Set.range (integerResonanceFrobeniusSolution r b ξ hP)) = ⊤ := by
  apply Submodule.map_injective_of_injective
    (polynomialLogLaurentSolutionSpace r b ξ).injective_subtype
  rw [Submodule.map_subtype_top,Submodule.map_span,← Set.range_comp]
  exact integerResonanceFrobeniusCoefficients_span_eq_solutionSpace r b ξ hP

def integerResonanceFrobeniusBasis
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Basis (polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) K
      (polynomialLogLaurentSolutionSpace r b ξ) :=
  Basis.mk (integerResonanceFrobeniusSolution_linearIndependent r b ξ hP)
    (integerResonanceFrobeniusSolution_span_eq_top r b ξ hP).ge

theorem integerResonanceFrobeniusBasis_apply
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    integerResonanceFrobeniusBasis r b ξ hP i = integerResonanceFrobeniusSolution r b ξ hP i :=
  Basis.mk_apply _ _ i

theorem polynomialLogLaurentSolutionSpace_finiteDimensional
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    FiniteDimensional K (polynomialLogLaurentSolutionSpace r b ξ) :=
  Module.Finite.of_basis (integerResonanceFrobeniusBasis r b ξ hP)

theorem polynomialLogLaurentSolutionSpace_finrank_eq_integerResonanceCost
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Module.finrank K (polynomialLogLaurentSolutionSpace r b ξ) =
      polynomialIntegerResonanceCost ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) := by
  rw [← polynomialLogIntegerResonanceIndex_card]
  exact Module.finrank_eq_card_basis (integerResonanceFrobeniusBasis r b ξ hP)

theorem polynomialLogLaurentSolution_existsUnique_integer_expansion
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    ∃! c : polynomialLogIntegerResonanceIndex ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) → K,
      s = ∑ i,c i • integerResonanceFrobeniusCoefficients
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ i := by
  let v : polynomialLogLaurentSolutionSpace r b ξ := ⟨s,hs⟩
  let basis := integerResonanceFrobeniusBasis r b ξ hP
  have h := basis.sum_repr v
  have hc := congrArg (polynomialLogLaurentSolutionSpace r b ξ).subtype h
  simp only [map_sum,map_smul,basis,integerResonanceFrobeniusBasis_apply] at hc
  refine ⟨fun i => basis.repr v i,hc.symm,?_⟩
  intro d hd
  apply funext
  apply (Fintype.linearIndependent_iffₛ.mp
    (integerResonanceFrobeniusCoefficients_linearIndependent _ ξ))
  exact hd.symm.trans hc.symm

end StrictEUnit
end

#print axioms StrictEUnit.integerResonanceFrobeniusSolution_linearIndependent
#print axioms StrictEUnit.integerResonanceFrobeniusSolution_span_eq_top
#print axioms StrictEUnit.integerResonanceFrobeniusBasis_apply
#print axioms StrictEUnit.polynomialLogLaurentSolutionSpace_finiteDimensional
#print axioms StrictEUnit.polynomialLogLaurentSolutionSpace_finrank_eq_integerResonanceCost
#print axioms StrictEUnit.polynomialLogLaurentSolution_existsUnique_integer_expansion
