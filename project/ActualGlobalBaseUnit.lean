import GlobalClassBaseEquation

noncomputable section
open scoped Classical
namespace StrictEUnit

def actualNaturalLogMatrix {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (xi : AlgebraicComplex) :
    Matrix (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      AlgebraicComplex := by
  exact naturalResonanceLogMatrix nu (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)

theorem actualNaturalLogMatrix_nilpotent {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (xi : AlgebraicComplex) : IsNilpotent (actualNaturalLogMatrix A hf hc xi) := by
  exact naturalResonanceLogMatrix_isNilpotent nu
    (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)

/-- An actual external-power/logarithm unit over the finite Laurent-log base,
with the exact manuscript differential equation, indexed by the retained rank. -/
theorem actualFourier_global_base_unit {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    ∃ xi : ExponentClass rho → AlgebraicComplex, ∃ s : Fin nu → ℕ,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu,
      (∀ j, rho j = xi (exponentClassMap rho j) + (s j : AlgebraicComplex)) ∧
      (∀ i, E i = e (naturalResonanceRootSeed _ (xi i.1)
        (sameFourierEulerIndicial_ne_zero A hf hc) i.2)) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ m : ExponentClass rho → ℤ,
      (∀ c, (m c : AlgebraicComplex) / (N : AlgebraicComplex) = xi c) ∧
      ∃ Z : (Matrix (Fin nu) (Fin nu) (LaurentLogBase AlgebraicComplex))ˣ,
      Z = @reindexedClassBaseUnit AlgebraicComplex (ExponentClass rho)
        (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
        (Fin nu) _ _ (Fintype.ofFinite _) _ _ _ _ _ m
        (fun c => actualNaturalLogMatrix A hf hc (xi c))
        (fun c => actualNaturalLogMatrix_nilpotent A hf hc (xi c)) E ∧
      matrixDerivative (manuscriptBaseDerivation N) Z.val =
        ramifiedConstantMatrix
          (@reindexedClassResidue AlgebraicComplex (ExponentClass rho)
            (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
            (Fin nu) _ (Fintype.ofFinite _) _ _ _ _ _ xi
            (fun c => actualNaturalLogMatrix A hf hc (xi c)) E) * Z.val := by
  obtain ⟨xi,s,E,hs,hsep,hE,N,hN,m,hm,hblocks⟩ :=
    actualFourier_rational_class_base_units A hf hc e rho hrho hroot
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  let L := fun c => actualNaturalLogMatrix A hf hc (xi c)
  let hL := fun c => actualNaturalLogMatrix_nilpotent A hf hc (xi c)
  refine ⟨xi,s,E,hs,hE,N,hN,m,hm,reindexedClassBaseUnit m L hL E,rfl,?_⟩
  exact reindexedClassBaseUnit_equation N hN.ne' xi m hm L hL E

end StrictEUnit
end
