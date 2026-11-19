import ActualGlobalBaseUnit
import GlobalClassResidueSpectrum

noncomputable section
open scoped Classical
namespace StrictEUnit

theorem rational_of_integer_quotient {K : Type*} [Field K] [CharZero K]
    (m : ℤ) (N : ℕ) (x : K) (h : (m : K) / (N : K) = x) :
    ∃ q : ℚ, (q : K) = x := by
  refine ⟨(m : ℚ) / (N : ℚ), ?_⟩
  simpa using h

theorem actualFourier_global_residue_rational {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (rho : Fin nu → AlgebraicComplex)
    (xi : ExponentClass rho → AlgebraicComplex)
    (E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu)
    (N : ℕ) (m : ExponentClass rho → ℤ)
    (hm : ∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c)
    (a : AlgebraicComplex)
    (ha : (minpoly AlgebraicComplex
      (@reindexedClassResidue AlgebraicComplex (ExponentClass rho)
        (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
        (Fin nu) _ (Fintype.ofFinite _) _ _ _ _ _ xi
        (fun c => actualNaturalLogMatrix A hf hc (xi c)) E)).IsRoot a) :
    ∃ q : ℚ, (q : AlgebraicComplex) = a := by
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  exact reindexedClassResidue_rational_spectrum xi
    (fun c => rational_of_integer_quotient (m c) N (xi c) (hm c))
    (fun c => actualNaturalLogMatrix A hf hc (xi c))
    (fun c => actualNaturalLogMatrix_nilpotent A hf hc (xi c)) E a ha
end StrictEUnit
end
