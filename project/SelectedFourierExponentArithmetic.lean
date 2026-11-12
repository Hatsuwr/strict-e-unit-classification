import SelectedFourierIndicialFactor
import SelectedSourceRootBinomialArithmetic
import SelectedConstructedTwistedAmplitudes
import FourierFiniteExponentArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- ALL actual roots of the literal SAME Fourier Euler indicial polynomial
have binomial prefix denominators. Source order r and Fourier degree nu remain
separate; their precise factorization is proved, not supplied. -/
def SameClearingFourierIndicialArithmeticData
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
    (sameFourierEulerCoefficientSymbols A hf 0).eval ξ=0 → BinomialPrefixDenominators ξ

theorem selectedFuchsSourceData_fourier_indicial_root_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingFourierIndicialArithmeticData φ n T UI := by
  have hQ := selectedFuchsSourceData_source_root_binomial_arithmetic G a φ n hr c T UI E hsource
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,hrest⟩ := hsource
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let q := sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U
  let p : Fin (n+2) → Polynomial AlgebraicComplex := fun i => (q i).map φ
  let qplus := ordinaryReflectionTuple (n+1) p
  let d := reciprocalCommonDegree (n+1) qplus
  let s := d-t.natTrailingDegree+(n+1)+1
  let A := reciprocalSourceArray (n+1) d qplus
  let τ := t.coeff t.natTrailingDegree
  let Q := regularResidueIndicial n (φ τ) (fun j => φ (polynomialCompanionFace n 1 1 t U j))
  let γ : AlgebraicComplex := (-1:AlgebraicComplex)^(s+t.natTrailingDegree+(n+1))*φ τ
  change ∀ hf : Stage56FiniteFuchs A,∀ ξ : AlgebraicComplex,
    (sameFourierEulerCoefficientSymbols A hf 0).eval ξ=0 → BinomialPrefixDenominators ξ
  intro hf ξ hξ
  have hfac := sameCompanion_mapped_reflected_indicial_factor φ n t U hT hpReg hf
  change sameFourierEulerCoefficientSymbols A hf 0=Polynomial.C γ*descPochhammer AlgebraicComplex s*Q at hfac
  have hγ : γ ≠ 0 := mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    ((map_ne_zero φ).2 (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT))
  exact binomialPrefixDenominators_of_indicial_factorization
    (sameFourierEulerCoefficientSymbols A hf 0) Q γ s hfac hγ hQ ξ hξ

/-- Same full formal Fin nu packet and literal amplitudes, with exponent
binomial arithmetic appended under the very same existential witnesses. -/
def SelectedFourierExponentArithmeticData
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
  FourierFiniteTwistedAmplitudeExponentArithmeticData A

theorem selectedFourierTwistedAmplitudeData_with_exponent_arithmetic
    {K : Type*} [Field K] [NumberField K] (φ : K →+* AlgebraicComplex)
    (n : ℕ) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hdata : SelectedFourierTwistedAmplitudeData φ (n+1) (Nat.succ_pos n) T UI)
    (hAll : SameClearingFourierIndicialArithmeticData φ n T UI) :
    SelectedFourierExponentArithmeticData φ n T UI := by
  exact fourierFiniteTwistedAmplitudeData_with_exponent_arithmetic _ hdata hAll

end StrictEUnit
end
