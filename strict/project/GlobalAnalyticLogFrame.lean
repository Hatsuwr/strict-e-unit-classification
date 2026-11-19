import ReindexedBlockUnit

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
local instance : CommRing (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield) :=
  (subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield).toCommRing

def GlobalAnalyticLogFrameData {nu : ℕ} (P : Polynomial AlgebraicComplex)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (xi : ExponentClass rho → AlgebraicComplex)
    (E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) ≃ Fin nu) : Prop :=
    ∃ F : Fin nu → subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
    ∃ Z : (Matrix (Fin nu) (Fin nu) (Polynomial (LaurentSeries AlgebraicComplex)))ˣ,
      (∀ i, IsStrictEFunction (F i).val.val) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : AlgebraicComplex)) ∧
      (∀ j, rho j = xi (E.symm j).1 + ((E.symm j).2.1.1 : AlgebraicComplex)) ∧
      ∀ j, frobeniusIntegerShift ((E.symm j).2.1.1 : ℤ) (p j) =
        ∑ i : Fin nu, analyticLaurentLogImage (F i) *
          Z.val i j

/-- The entire strict-E row and square invertible logarithmic factor are now
indexed by exactly the original retained family, not by an enlarged list. -/
theorem fourierRetainedArithmeticData_analytic_block_unit {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j)) (xi : AlgebraicComplex) :
    ∃ F : polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0) →
      subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield,
    ∃ Z : (Matrix (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
      (Polynomial (LaurentSeries AlgebraicComplex)))ˣ,
      (∀ i, IsStrictEFunction (F i).val.val) ∧
      ∀ j, naturalResonanceFrobeniusAmplitude (sameFourierEulerCoefficientSymbols A hf) xi j =
      ∑ i, analyticLaurentLogImage (F i) * Z.val i j := by
  obtain ⟨F, hF, hrow⟩ := fourierRetainedArithmeticData_analytic_square_block A ha hf hc e rho p hrho hp xi
  let N := naturalResonanceLogMatrix nu (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)
  let hN := naturalResonanceLogMatrix_isNilpotent nu (fun k => (stage61_fourierLift A hf).coeff k.val) xi
    (sameFourierEulerIndicial_ne_zero A hf hc)
  let f : Polynomial AlgebraicComplex →+* Polynomial (LaurentSeries AlgebraicComplex) :=
    Polynomial.mapRingHom (algebraMap AlgebraicComplex (LaurentSeries AlgebraicComplex))
  let Z : (Matrix (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (polynomialLogResonanceCoordinateIndex xi (sameFourierEulerCoefficientSymbols A hf 0))
    (Polynomial (LaurentSeries AlgebraicComplex)))ˣ :=
    Units.map f.mapMatrix.toMonoidHom (finiteLogMatrixUnit N hN)
  refine ⟨F, Z, hF, ?_⟩
  intro j
  exact hrow j

theorem fourierRetainedArithmeticData_global_analytic_log_frame {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j)) :
    ∃ xi : ExponentClass rho → AlgebraicComplex,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu,
    GlobalAnalyticLogFrameData (sameFourierEulerCoefficientSymbols A hf 0) rho p xi E := by
  obtain ⟨xi, hsep, E, hexp, hamp, hcard⟩ := actualFourier_disjoint_class_assembly A hf hc e rho p hrho hp
  letI : Fintype (ExponentClass rho) := Fintype.ofFinite _
  have hh := fun c => fourierRetainedArithmeticData_analytic_block_unit A ha hf hc e rho p hrho hp (xi c)
  choose F Z1 hF hrow using hh
  refine ⟨xi, E, ?_⟩
  unfold GlobalAnalyticLogFrameData
  let Zg := reindexedBlockUnit (C := ExponentClass rho)
    (I := fun c => polynomialLogResonanceCoordinateIndex (xi c) (sameFourierEulerCoefficientSymbols A hf 0))
    (J := Fin nu) (R := Polynomial (LaurentSeries AlgebraicComplex)) Z1 E
  refine ⟨(fun i => F (E.symm i).1 (E.symm i).2), Zg,
    (fun i => hF _ _), hsep, ?_, ?_⟩
  · intro j
    simpa only [Equiv.apply_symm_apply] using hexp (E.symm j)
  · intro j
    dsimp only [Zg]
    have hglue := reindexedBlockUnit_analytic_row Z1 E F j
    rw [hglue]
    have h := hrow (E.symm j).1 (E.symm j).2
    have ham := hamp (E.symm j)
    simp only [Equiv.apply_symm_apply] at ham
    rw [← ham]
    exact h

end StrictEUnit
end
