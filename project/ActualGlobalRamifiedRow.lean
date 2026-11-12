import MappedBlockScalarRow
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem actualNaturalAmplitude_retained_shift {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (hf : Stage56FiniteFuchs A) (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (xi : AlgebraicComplex)
    (i : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (j : Fin nu) (hj : j = e (naturalResonanceRootSeed _ xi
      (sameFourierEulerIndicial_ne_zero A hf hc) i)) :
    naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi i =
      frobeniusIntegerShift (i.1.1 : ℤ) (p j) := by
  rw [hj, hp, Equiv.symm_apply_apply]
  rfl


theorem actualFourier_global_ramified_row {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (xi : ExponentClass rho → AlgebraicComplex)
    (E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu)
    (hE : ∀ i, E i = e (naturalResonanceRootSeed _ (xi i.1)
      (sameFourierEulerIndicial_ne_zero A hf hc) i.2))
    (N : ℕ) (hN : N ≠ 0) (m : ExponentClass rho → ℤ) :
    ∃ F : Fin nu → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
      (∀ i, IsStrictEFunction (F i).val.val) ∧
      ∀ j, (∑ i : Fin nu, Polynomial.C (show LaurentSeries AlgebraicComplex from
        stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
          (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F i))) *
        laurentLogToSeriesPolynomial
          ((@reindexedClassBaseUnit AlgebraicComplex (ExponentClass rho)
            (fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
            (Fin nu) _ _ (Fintype.ofFinite _) _ _ _ _ _ m
            (fun c => actualNaturalLogMatrix A hf hc (xi c))
            (fun c => actualNaturalLogMatrix_nilpotent A hf hc (xi c)) E).val i j)) =
        Polynomial.C (HahnSeries.single
          (m (E.symm j).1 + (N : ℤ) * ((E.symm j).2.1.1 : ℤ)) (1 : AlgebraicComplex)) *
          stage38_logRamification N hN (p j) := by
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  choose F hF hrow using fun c => actualFourier_ramified_analytic_block
    A ha hf hc e rho p hrho hp (xi c) N hN (m c)
  refine ⟨fun j => F (E.symm j).1 (E.symm j).2, fun j => hF _ _, ?_⟩
  intro j
  have hg := mapped_reindexedBlockUnit_row laurentLogToSeriesPolynomial
    (fun c => fixedExponentBaseUnit (m c) (actualNaturalLogMatrix A hf hc (xi c))
      (actualNaturalLogMatrix_nilpotent A hf hc (xi c))) E
    (fun c i => Polynomial.C (show LaurentSeries AlgebraicComplex from
      stage14_subfieldEntireLaurentAlgHom (algebraicClosure ℚ ℂ).toSubfield
        (stage17_arithmeticPowerPullback (algebraicClosure ℚ ℂ).toSubfield N hN (F c i)))) j
  refine hg.trans ?_
  rw [← hrow (E.symm j).1 (E.symm j).2]
  have he := actualNaturalAmplitude_retained_shift A hf hc e p hp
    (xi (E.symm j).1) (E.symm j).2 j
    ((E.apply_symm_apply j).symm.trans (hE (E.symm j)))
  rw [he, ramified_external_natural_shift]
end StrictEUnit
end
