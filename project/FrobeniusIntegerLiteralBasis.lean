import FrobeniusIntegerResonanceBasis

/-! Transport the proved fixed basis to the literal polynomial-log ring.
Membership remains equivalent to the actual ring differential equation. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def polynomialLogLiteralSolutionSpace (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) :
    Submodule K (Polynomial (LaurentSeries K)) :=
  (polynomialLogLaurentSolutionSpace r b ξ).comap logPolynomialCoefficientLinear

theorem polynomialLogLiteralSolutionSpace_mem_iff
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) (p : Polynomial (LaurentSeries K)) :
    p ∈ polynomialLogLiteralSolutionSpace r b ξ ↔ scalarTwistedLogOperator r b ξ p = 0 := by
  change scalarTwistedCoefficientOperator r b ξ (logPolynomialToCoefficientSeries p) = 0 ↔ _
  rw [← logPolynomialToCoefficientSeries_scalarTwistedCoefficientOperator]
  constructor
  · intro h
    exact logPolynomialToCoefficientSeries_injective (h.trans (map_zero _).symm)
  · intro h
    rw [h,map_zero]

def polynomialLogSolutionRepresentation (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) :
    polynomialLogLiteralSolutionSpace r b ξ →ₗ[K] polynomialLogLaurentSolutionSpace r b ξ where
  toFun p := ⟨logPolynomialCoefficientLinear p.1,p.2⟩
  map_add' p q := Subtype.ext (map_add logPolynomialCoefficientLinear p.1 q.1)
  map_smul' c p := Subtype.ext (logPolynomialCoefficientLinear.map_smul c p.1)

theorem polynomialLogSolutionRepresentation_bijective
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Function.Bijective (polynomialLogSolutionRepresentation r b ξ) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply logPolynomialToCoefficientSeries_injective
    exact congrArg Subtype.val hpq
  · intro s
    obtain ⟨p,⟨hp,he⟩,-⟩ := polynomialLogLaurentSolution_existsUnique_realization
      r b ξ hP s.1 s.2
    exact ⟨⟨p,(polynomialLogLiteralSolutionSpace_mem_iff r b ξ p).mpr he⟩,Subtype.ext hp⟩

def polynomialLogSolutionRepresentationEquiv
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    polynomialLogLiteralSolutionSpace r b ξ ≃ₗ[K] polynomialLogLaurentSolutionSpace r b ξ :=
  LinearEquiv.ofBijective (polynomialLogSolutionRepresentation r b ξ)
    (polynomialLogSolutionRepresentation_bijective r b ξ hP)

def integerResonanceLiteralSolution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    polynomialLogLiteralSolutionSpace r b ξ :=
  ⟨integerResonanceFrobeniusAmplitude _ ξ i,by
    change scalarTwistedCoefficientOperator r b ξ
      (logPolynomialToCoefficientSeries (integerResonanceFrobeniusAmplitude _ ξ i)) = 0
    rw [integerResonanceFrobeniusAmplitude_representation]
    exact integerResonanceFrobeniusCoefficients_solution r b ξ hP i⟩

def integerResonanceLiteralBasis
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Basis (polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) K
      (polynomialLogLiteralSolutionSpace r b ξ) :=
  (integerResonanceFrobeniusBasis r b ξ hP).map
    (polynomialLogSolutionRepresentationEquiv r b ξ hP).symm

theorem integerResonanceLiteralBasis_apply
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogIntegerResonanceIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    integerResonanceLiteralBasis r b ξ hP i = integerResonanceLiteralSolution r b ξ hP i := by
  apply (polynomialLogSolutionRepresentationEquiv r b ξ hP).injective
  rw [integerResonanceLiteralBasis,Basis.map_apply,LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [integerResonanceFrobeniusBasis_apply]
  exact (integerResonanceFrobeniusAmplitude_representation _ ξ i).symm

theorem polynomialLogLiteralSolutionSpace_finrank_eq_integerResonanceCost
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Module.finrank K (polynomialLogLiteralSolutionSpace r b ξ) =
      polynomialIntegerResonanceCost ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) := by
  rw [← polynomialLogIntegerResonanceIndex_card]
  exact Module.finrank_eq_card_basis (integerResonanceLiteralBasis r b ξ hP)

theorem polynomialLogLiteralSolution_existsUnique_integer_expansion
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (p : Polynomial (LaurentSeries K)) (hp : scalarTwistedLogOperator r b ξ p = 0) :
    ∃! c : polynomialLogIntegerResonanceIndex ξ
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0) → K,
      p = Fintype.linearCombination K (integerResonanceFrobeniusAmplitude
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ) c := by
  let v : polynomialLogLiteralSolutionSpace r b ξ :=
    ⟨p,(polynomialLogLiteralSolutionSpace_mem_iff r b ξ p).mpr hp⟩
  let basis := integerResonanceLiteralBasis r b ξ hP
  have h := basis.sum_repr v
  have hc := congrArg (polynomialLogLiteralSolutionSpace r b ξ).subtype h
  simp only [map_sum,LinearMap.map_smul,basis,integerResonanceLiteralBasis_apply] at hc
  have hc' : p = Fintype.linearCombination K (integerResonanceFrobeniusAmplitude
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ)
      (fun i => basis.repr v i) := by
    simpa only [Fintype.linearCombination_apply] using hc.symm
  refine ⟨fun i => basis.repr v i,hc',?_⟩
  intro d hd
  exact (integerResonanceFrobeniusAmplitude_linearIndependent _ ξ).fintypeLinearCombination_injective
    (hd.symm.trans hc')

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogLiteralSolutionSpace_mem_iff
#print axioms StrictEUnit.polynomialLogSolutionRepresentation_bijective
#print axioms StrictEUnit.integerResonanceLiteralBasis_apply
#print axioms StrictEUnit.polynomialLogLiteralSolutionSpace_finrank_eq_integerResonanceCost
#print axioms StrictEUnit.polynomialLogLiteralSolution_existsUnique_integer_expansion
