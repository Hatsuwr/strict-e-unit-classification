import NaturalResonanceStrictLogFreeRow

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem fourierRetainedArithmeticData_analytic_square_block {mu nu : ℕ}
    (A : Fin (mu+1) →Fin (nu+1) →AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu)≠0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu →AlgebraicComplex) (p : Fin nu →Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ i,rho i=frobeniusRootSeedExponent _ (e.symm i))
    (hp : ∀ i,p i=sameFourierTwistedAmplitude A hf (e.symm i))
    (xi : AlgebraicComplex) :
    let b := fun k : Fin (nu+1) =>(stage61_fourierLift A hf).coeff k.val
    let hP := sameFourierEulerIndicial_ne_zero A hf hc
    let N := naturalResonanceLogMatrix nu b xi hP
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
        subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i,IsStrictEFunction (F i).val.val) ∧
      ∀ j,naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j=
        ∑ i,Polynomial.C (show LaurentSeries AlgebraicComplex from stage14_subfieldEntireLaurentAlgHom
          (algebraicClosure ℚ ℂ).toSubfield (F i))*
          Polynomial.map (algebraMap AlgebraicComplex (LaurentSeries AlgebraicComplex))
            ((finiteLogMatrixUnit N (naturalResonanceLogMatrix_isNilpotent nu b xi hP)).val i j) := by
  dsimp only
  obtain ⟨F,hs,he⟩ := fourierRetainedArithmeticData_natural_logFree_row A ha hf hc e rho p hrho hp xi
  refine ⟨F,hs,?_⟩
  intro j
  simp only [he]
  exact naturalResonanceFrobeniusAmplitude_square_factorization nu
    (fun k =>(stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc) j
end StrictEUnit
end
