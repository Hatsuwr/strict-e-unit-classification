import SameCompanionLaurentShearTransport
import PowerSeriesEulerPochhammer
import SelectedFuchsSourceData

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Exact transport for the SAME original companion and scalar tuple. The
Laurent change of variables is invertible on every vector. For power series,
the inverse assertion is restricted by the actual Euler equation, which forces
weighted ordinary jets. No divisibility, solution-family or spectral premise
is part of this conclusion. -/
def SameClearingDifferentialShearData
    {K : Type*} [Field K] [NumberField K] (G : PowerSeries K)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  (∀ v,SameClearedLaurentCompanionSystem n t U v ↔
    SameLaurentEulerSystem n t U (companionLaurentShear n v)) ∧
  (∀ Y,SameLaurentEulerSystem n t U Y ↔
    SameClearedLaurentCompanionSystem n t U (companionLaurentUnshear n Y)) ∧
  (∀ f,sameCompanionPowerSeriesScalarAction n t U f=0 ↔
    ∀ i,powerSeriesEuler (weightedDerivativeJet i.val f)=
      (sameCompanionEulerPowerSeriesMatrix n t U *ᵥ (fun j => weightedDerivativeJet j.val f)) i) ∧
  (∀ Y : Fin (n+1) → PowerSeries K,
    (∀ i,powerSeriesEuler (Y i)=(sameCompanionEulerPowerSeriesMatrix n t U *ᵥ Y) i) ↔
    (∀ i,Y i=weightedDerivativeJet i.val (Y 0)) ∧
      sameCompanionPowerSeriesScalarAction n t U (Y 0)=0) ∧
  (∀ i,powerSeriesEuler (weightedDerivativeJet i.val G)=
    (sameCompanionEulerPowerSeriesMatrix n t U *ᵥ (fun j => weightedDerivativeJet j.val G)) i) ∧
  (sameCompanionEulerPochhammerPolynomial n t U).map (PowerSeries.constantCoeff K)=
    regularResidueIndicial n (t.coeff t.natTrailingDegree) (polynomialCompanionFace n 1 1 t U) ∧
  (sameCompanionEulerPochhammerPolynomial n t U).Monic ∧
  (sameCompanionEulerPochhammerPolynomial n t U).natDegree=n+1

/-- All transport and the actual original G solution are derived from the
original source packet. In particular the regular inequalities are proved from
its original common denominators, rather than supplied as another input. The
proof has no positive trailing-order assumption and includes ordinary zero. -/
theorem selectedFuchsSourceData_differential_shear
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingDifferentialShearData G n T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  have hV := companion_common_denominators_local_bounds n c _ _ hT hclear E hE hden
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  have heq (f : PowerSeries K) :=
    sameCompanionPowerSeriesScalarAction_eq_zero_iff_euler n t U hT hV f
  have hG : sameCompanionPowerSeriesScalarAction n t U G=0 :=
    powerSeries_equation_of_laurent_scalar_equation G (n+1)
      (sameCompanionScalarTuple (n+1) hr t U) hann
  refine ⟨sameCompanionLaurentShear_system_iff n c t U hT hclear hV,
    sameCompanionLaurentUnshear_system_iff n c t U hT hclear hV,heq,?_,
    (heq G).1 hG,sameCompanionEulerPochhammerPolynomial_constantCoeff n t U,
    sameCompanionEulerPochhammerPolynomial_monic n t U,
    sameCompanionEulerPochhammerPolynomial_natDegree n t U⟩
  intro Y
  constructor
  · intro hY
    exact ⟨sameCompanionPowerSeriesEulerSolution_eq_jets n t U Y hY,
      sameCompanionPowerSeriesEulerSolution_scalar n t U hT hV Y hY⟩
  · rintro ⟨hj,hs⟩
    have hh := (heq (Y 0)).1 hs
    intro i
    simpa only [← hj] using hh i

end StrictEUnit
end
