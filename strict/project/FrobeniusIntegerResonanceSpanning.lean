import FrobeniusIntegerResonanceIndependence

/-! A solution-dependent normalization is used only in the proof. The target
family is one fixed all-integer-resonance family, independent of the solution. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Insert the natural resonances above any integer cutoff into the ONE fixed
all-integer resonance index. -/
def naturalToIntegerResonanceIndex (ξ : K) (P : Polynomial K) (k : ℤ)
    (i : polynomialLogResonanceCoordinateIndex (ξ+(k : K)) P) :
    polynomialLogIntegerResonanceIndex ξ P :=
  ⟨⟨k+(i.1.1 : ℤ),(polynomialIntegerResonanceIndices_mem ξ P _).mpr (by
      have h := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.2.1) i.2.isLt)
      simpa only [polynomialResonanceMultiplicity,Int.cast_add,Int.cast_natCast,add_assoc] using h)⟩,
    ⟨i.2.1,by
      simpa only [polynomialResonanceMultiplicity,Int.cast_add,Int.cast_natCast,add_assoc]
        using i.2.isLt⟩⟩

theorem naturalToIntegerResonanceIndex_amplitude (B : ℕ → Polynomial K) (ξ : K) (k : ℤ)
    (i : polynomialLogResonanceCoordinateIndex (ξ+(k : K)) (B 0)) :
    frobeniusIntegerShift k (naturalResonanceFrobeniusAmplitude B (ξ+(k : K)) i) =
      integerResonanceFrobeniusAmplitude B ξ (naturalToIntegerResonanceIndex ξ (B 0) k i) := by
  simp only [naturalResonanceFrobeniusAmplitude,integerResonanceFrobeniusAmplitude,
    naturalToIntegerResonanceIndex,frobeniusIntegerShift_add,Int.cast_add,Int.cast_natCast,add_assoc]

theorem naturalToIntegerResonanceIndex_coefficients (B : ℕ → Polynomial K) (ξ : K) (k : ℤ)
    (i : polynomialLogResonanceCoordinateIndex (ξ+(k : K)) (B 0)) :
    laurentCoefficientShift k (powerSeriesCoefficientEmbedding
      (naturalResonanceFrobeniusCoefficients B (ξ+(k : K)) i)) =
      integerResonanceFrobeniusCoefficients B ξ (naturalToIntegerResonanceIndex ξ (B 0) k i) := by
  rw [← integerResonanceFrobeniusAmplitude_representation,
    ← naturalToIntegerResonanceIndex_amplitude,logPolynomialToCoefficientSeries_integerShift,
    naturalResonanceFrobeniusAmplitude_representation]
  rfl

/-- Every actual Laurent solution belongs to the span of one FIXED finite
family. No solution-dependent family is left in this conclusion. -/
theorem polynomialLogLaurentSolution_mem_integerResonance_span
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (s : LaurentSeries (Polynomial K)) (hs : scalarTwistedCoefficientOperator r b ξ s = 0) :
    s ∈ Submodule.span K (Set.range (integerResonanceFrobeniusCoefficients
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ)) := by
  let B := scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))
  let L := (laurentCoefficientShiftLinear (K := K) s.order).comp powerSeriesCoefficientEmbedding
  obtain ⟨c,hc,-⟩ := polynomialLogLaurentSolution_existsUnique_normalized_expansion r b ξ hP s hs
  have hrep : L (laurentNormalizedCoefficients s) = s :=
    laurentNormalizedCoefficients_representation s
  rw [← hrep]
  rw [hc,map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  apply Submodule.smul_mem
  change laurentCoefficientShift s.order (powerSeriesCoefficientEmbedding
    (naturalResonanceFrobeniusCoefficients B (ξ+(s.order : K)) i)) ∈ _
  rw [naturalToIntegerResonanceIndex_coefficients]
  exact Submodule.subset_span ⟨naturalToIntegerResonanceIndex ξ (B 0) s.order i,rfl⟩

/-- The actual differential kernel equals the span of the fixed integer family. -/
theorem integerResonanceFrobeniusCoefficients_span_eq_solutionSpace
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    Submodule.span K (Set.range (integerResonanceFrobeniusCoefficients
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ)) =
      polynomialLogLaurentSolutionSpace r b ξ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro s ⟨i,rfl⟩
    exact integerResonanceFrobeniusCoefficients_solution r b ξ hP i
  · intro s hs
    exact polynomialLogLaurentSolution_mem_integerResonance_span r b ξ hP s hs

end StrictEUnit
end

#print axioms StrictEUnit.naturalToIntegerResonanceIndex_amplitude
#print axioms StrictEUnit.naturalToIntegerResonanceIndex_coefficients
#print axioms StrictEUnit.polynomialLogLaurentSolution_mem_integerResonance_span
#print axioms StrictEUnit.integerResonanceFrobeniusCoefficients_span_eq_solutionSpace
