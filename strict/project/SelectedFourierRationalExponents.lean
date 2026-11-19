import RationalExponentRamification
import SelectedFourierRetainedArithmetic
import GlobalAnalyticLogFrame

noncomputable section
open scoped NumberField Matrix
namespace StrictEUnit

def SameClearingFourierRationalExponentData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map φ
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let A := reciprocalSourceArray (n+1) d qplus
  ∀ hf : Stage56FiniteFuchs A,∀ ξ : AlgebraicComplex,
    (sameFourierEulerCoefficientSymbols A hf 0).eval ξ=0 → ∃ q : ℚ, algebraMap ℚ AlgebraicComplex q = ξ

/-- Rationality of every root of the SAME selected reflected-reciprocal
Fourier indicial polynomial, derived directly from the original source packet. -/
theorem selectedFuchsSourceData_fourier_rational_exponents
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingFourierRationalExponentData phi n T UI := by
  have h := selectedFuchsSourceData_fourier_indicial_root_arithmetic G a phi n hr c T UI E hsource
  intro hf xi hx
  exact algebraicComplex_binomialPrefixDenominators_rational xi (h hf xi hx)

/-- A single derived ramification clears both the retained external exponents
and the shifted class exponents actually used in every original-rank column. -/
theorem globalAnalyticLogFrameData_integer_exponents
    {nu : ℕ} (P : Polynomial AlgebraicComplex)
    (rho : Fin nu → AlgebraicComplex) (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (xi : ExponentClass rho → AlgebraicComplex)
    (E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) ≃ Fin nu)
    (h : GlobalAnalyticLogFrameData P rho p xi E)
    (hr : JointBinomialPrefixDenominators rho) :
    ∃ N : ℕ, 0 < N ∧ ∃ z w : Fin nu → ℤ,
      (∀ j, (N : AlgebraicComplex) * rho j = (z j : AlgebraicComplex)) ∧
      (∀ j, (N : AlgebraicComplex) * xi (E.symm j).1 = (w j : AlgebraicComplex)) := by
  obtain ⟨r,hrat,N,hN,z,hz⟩ := jointBinomialPrefixDenominators_rational_ramification rho hr
  obtain ⟨F,Z,hF,hsep,hexp,hrow⟩ := h
  refine ⟨N,hN,z,fun j => z j - (N : ℤ) * ((E.symm j).2.1.1 : ℤ),hz,?_⟩
  intro j
  have hh := hz j
  rw [hexp j] at hh
  push_cast
  linear_combination hh

theorem fourierRetainedArithmeticData_rational_global_log_frame {mu nu : ℕ}
    (A : Fin (mu+1) → Fin (nu+1) → AlgebraicComplex)
    (ha : FourierRetainedArithmeticData A) (hf : Stage56FiniteFuchs A)
    (hc : A (Fin.last mu) (Fin.last nu) ≠ 0)
    (e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin nu)
    (rho : Fin nu → AlgebraicComplex)
    (p : Fin nu → Polynomial (LaurentSeries AlgebraicComplex))
    (hrho : ∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j))
    (hp : ∀ j, p j = sameFourierTwistedAmplitude A hf (e.symm j))
    (hroot : ∀ x, (sameFourierEulerCoefficientSymbols A hf 0).eval x = 0 →
      BinomialPrefixDenominators x) :
    ∃ xi : ExponentClass rho → AlgebraicComplex,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin nu,
    GlobalAnalyticLogFrameData (sameFourierEulerCoefficientSymbols A hf 0) rho p xi E ∧
    ∃ N : ℕ, 0 < N ∧ ∃ z w : Fin nu → ℤ,
      (∀ j, (N : AlgebraicComplex) * rho j = (z j : AlgebraicComplex)) ∧
      (∀ j, (N : AlgebraicComplex) * xi (E.symm j).1 = (w j : AlgebraicComplex)) := by
  obtain ⟨xi,E,hframe⟩ := fourierRetainedArithmeticData_global_analytic_log_frame
    A ha hf hc e rho p hrho hp
  refine ⟨xi,E,hframe,?_⟩
  apply globalAnalyticLogFrameData_integer_exponents _ rho p xi E hframe
  apply finite_binomialPrefixDenominators
  intro j
  apply hroot
  rw [hrho j]
  exact frobeniusRootSeedExponent_isRoot _ (e.symm j)

def SameClearingFourierRationalGlobalFrameData
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map φ
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let ν := reciprocalSourceDegree (n+1) d qplus
  let A := reciprocalSourceArray (n+1) d qplus
  ∀ hf : Stage56FiniteFuchs A, A (Fin.last (n+1)) (Fin.last ν) ≠ 0 →
  ∀ e : frobeniusRootSeedIndex (sameFourierEulerCoefficientSymbols A hf 0) ≃ Fin ν,
  ∀ rho : Fin ν → AlgebraicComplex,
  ∀ amp : Fin ν → Polynomial (LaurentSeries AlgebraicComplex),
    (∀ j, rho j = frobeniusRootSeedExponent _ (e.symm j)) →
    (∀ j, amp j = sameFourierTwistedAmplitude A hf (e.symm j)) →
    ∃ xi : ExponentClass rho → AlgebraicComplex,
    ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c)
      (sameFourierEulerCoefficientSymbols A hf 0)) ≃ Fin ν,
      GlobalAnalyticLogFrameData (sameFourierEulerCoefficientSymbols A hf 0) rho amp xi E ∧
      ∃ N : ℕ, 0 < N ∧ ∃ z w : Fin ν → ℤ,
        (∀ j, (N : AlgebraicComplex) * rho j = (z j : AlgebraicComplex)) ∧
        (∀ j, (N : AlgebraicComplex) * xi (E.symm j).1 = (w j : AlgebraicComplex))

theorem selectedFuchsSourceData_fourier_rational_global_frame
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    SameClearingFourierRationalGlobalFrameData phi n T UI := by
  have ha := selectedFuchsSourceData_fourier_retained_arithmetic G a phi n hr c T UI E hsource
  have hroot := selectedFuchsSourceData_fourier_indicial_root_arithmetic G a phi n hr c T UI E hsource
  intro hf hc e rho amp hrho hamp
  exact fourierRetainedArithmeticData_rational_global_log_frame _ ha hf hc e rho amp hrho hamp (hroot hf)

end StrictEUnit
end
