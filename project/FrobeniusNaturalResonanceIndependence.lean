import FrobeniusNaturalShiftCoefficients

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Natural shift and log-seed order recover the exact resonance index. -/
theorem polynomialLogResonanceCoordinateIndex_pair_injective
    (ξ : K) (P : Polynomial K) :
    Function.Injective (fun i : polynomialLogResonanceCoordinateIndex ξ P => (i.1.1,i.2.1)) := by
  rintro ⟨⟨n,hn⟩,i⟩ ⟨⟨m,hm⟩,j⟩ h
  have hnm : n = m := congrArg Prod.fst h
  subst m
  have hij : i = j := Fin.ext (congrArg Prod.snd h)
  subst j
  rfl

/-- Lowest nonzero shift detects a finite relation between actual coefficient
sequences. No representation or independence premise is supplied. -/
theorem naturalCoefficientShift_frobenius_linearIndependent
    {ι : Type*} [Fintype ι] (B : ℕ → Polynomial K) (rho : ι → K)
    (s j : ι → ℕ) (hinj : Function.Injective (fun i => (s i,j i))) :
    LinearIndependent K (fun i => naturalCoefficientShift (s i)
      (polynomialLogFrobeniusCoefficient B (rho i) (Polynomial.X ^ j i))) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  by_contra hci
  let S : Finset ι := Finset.univ.filter (fun k => c k ≠ 0)
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hci⟩⟩
  obtain ⟨i0,hi0,hmin⟩ := Finset.exists_min_image S s hS
  have hc0 : c i0 ≠ 0 := (Finset.mem_filter.mp hi0).2
  have hz := congrArg (fun u : ℕ → Polynomial K => (u (s i0)).coeff (j i0)) hc
  simp only [Finset.sum_apply,Pi.smul_apply,Polynomial.finset_sum_coeff,
    Polynomial.coeff_smul,Pi.zero_apply,Polynomial.coeff_zero] at hz
  have hlead : (naturalCoefficientShift (s i0)
      (polynomialLogFrobeniusCoefficient B (rho i0) (Polynomial.X ^ j i0))
        (s i0)).coeff (j i0) = 1 := by
    simp [naturalCoefficientShift]
  have hother (k : ι) (hki : k ≠ i0) :
      c k • (naturalCoefficientShift (s k)
        (polynomialLogFrobeniusCoefficient B (rho k) (Polynomial.X ^ j k))
          (s i0)).coeff (j i0) = 0 := by
    by_cases hck : c k = 0
    · simp only [hck,zero_smul]
    have hs : s i0 ≤ s k := hmin k
      (Finset.mem_filter.mpr ⟨Finset.mem_univ k,hck⟩)
    by_cases heq : s k = s i0
    · have hj : j k ≠ j i0 := by
        intro hj
        exact hki (hinj (Prod.ext heq hj))
      simp [naturalCoefficientShift,heq,Polynomial.coeff_X_pow,hj,Ne.symm hj]
    · have hnle : ¬ s k ≤ s i0 := not_le.mpr (lt_of_le_of_ne hs (Ne.symm heq))
      simp [naturalCoefficientShift,hnle]
  rw [Finset.sum_eq_single i0 (fun k _ hki => hother k hki)
    (fun h => (h (Finset.mem_univ i0)).elim),hlead,smul_eq_mul,mul_one] at hz
  exact hc0 hz

theorem naturalResonanceFrobeniusCoefficients_linearIndependent
    (B : ℕ → Polynomial K) (ξ : K) :
    LinearIndependent K (naturalResonanceFrobeniusCoefficients B ξ) := by
  apply naturalCoefficientShift_frobenius_linearIndependent
  exact polynomialLogResonanceCoordinateIndex_pair_injective ξ (B 0)

/-- The same sequences as members of the full equation-defined solution space. -/
def naturalResonanceFrobeniusSolution
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0)
    (i : polynomialLogResonanceCoordinateIndex ξ
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0)) :
    polynomialLogFormalSolutionSpace
      (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ :=
  ⟨naturalResonanceFrobeniusCoefficients _ ξ i,
    naturalResonanceFrobeniusCoefficients_solution r b ξ hP i⟩

theorem naturalResonanceFrobeniusSolution_linearIndependent
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (hP : scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i)) 0 ≠ 0) :
    LinearIndependent K (naturalResonanceFrobeniusSolution r b ξ hP) := by
  apply LinearIndependent.of_comp (polynomialLogFormalSolutionSpace _ ξ).subtype
  exact naturalResonanceFrobeniusCoefficients_linearIndependent _ ξ

end StrictEUnit
end

#print axioms StrictEUnit.polynomialLogResonanceCoordinateIndex_pair_injective
#print axioms StrictEUnit.naturalCoefficientShift_frobenius_linearIndependent
#print axioms StrictEUnit.naturalResonanceFrobeniusCoefficients_linearIndependent
#print axioms StrictEUnit.naturalResonanceFrobeniusSolution_linearIndependent
