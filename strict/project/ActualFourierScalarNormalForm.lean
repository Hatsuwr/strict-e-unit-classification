import ActualScalarNormalFormRow
import ActualGlobalResidueSpectrum
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem actualFourier_scalarNormalForm {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    Nonempty (Stage33ScalarNormalForm (algebraicClosure ℚ ℂ).toSubfield nu
      (stage53_fourierCoeff A)) := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨xi,s,E,hs,hE,N,hN,m,hm,Z,hZ,hODE⟩ :=
    actualFourier_global_base_unit A hf hc e rho hrho hroot
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  obtain ⟨F,hF,hrow⟩ := actualFourier_global_ramified_row A ha hf hc e rho p hrho hp
    xi E hE N hN.ne' m
  let M := reindexedClassResidue xi (fun c => actualNaturalLogMatrix A hf hc (xi c)) E
  let w : Fin nu → ℤ := fun j => m (E.symm j).1 + (N : ℤ) * ((E.symm j).2.1.1 : ℤ)
  have hw : ∀ j, (w j : AlgebraicComplex) / (N : AlgebraicComplex) = rho j := by
    intro j
    exact ramified_shift_quotient N hN.ne' _ _ _ _ (hm (E.symm j).1)
      (actualNaturalRoot_retained_exponent A hf hc e rho hrho _ _ j
        ((E.apply_symm_apply j).symm.trans (hE (E.symm j))))
  have hscalar : stage33_scalarNormalFormRow (algebraicClosure ℚ ℂ).toSubfield N hN.ne' F Z =
      fun j => stage38_logAmbient (Polynomial.C (HahnSeries.single (w j) (1 : AlgebraicComplex)) *
        stage38_logRamification N hN.ne' (p j)) := by
    funext j
    rw [scalarNormalFormRow_as_logAmbient, hZ]
    exact congrArg stage38_logAmbient (hrow j)
  refine ⟨⟨N, hN.ne', F, M, Z, hF, ?_, hODE, ?_, ?_⟩⟩
  · intro a ha
    exact actualFourier_global_residue_rational A hf hc rho xi E N m hm a ha
  · intro j
    rw [hscalar]
    have hh := actualFourier_ramified_ambient_equation (algebraicClosure ℚ ℂ).toSubfield
      A hf hc (e.symm j) N hN.ne' (w j) ((hw j).trans (hrho j))
    simpa only [hp j] using hh
  · rw [hscalar]
    exact actualFourier_ramified_ambient_independent A hf e rho p hrho hp N hN.ne' w hw
end StrictEUnit
end
