import SelectedFuchsSourceData
import SignedLaplaceBoundaryCoefficients

noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit

/-- Homogeneous source action forces the actual nu-cutoff boundary to vanish. -/
theorem signedLaplaceFirstNuBoundary_eq_zero_of_source_zero
    {K : Type*} [Field K] [CharZero K] {μ ν : ℕ}
    (A : Fin (μ+1) → Fin (ν+1) → K) (a : ℕ → K)
    (hs : signedLaplaceSourceAction A (signedOrdinarySource a) = 0) :
    signedLaplaceFirstNuBoundary A a = 0 := by
  rw [← signedLaplaceBoundaryPolynomial_eq_firstNu, signedLaplaceBoundaryPolynomial, hs]
  ext k
  rw [signedLaplaceKernelPolynomial_coeff_all, HahnSeries.coeff_zero, Polynomial.coeff_zero]

/-- The boundary and finite initial-value identities for precisely the SAME
selected reciprocal source array. Orders r and nu remain separate. -/
def SelectedFirstNuBoundaryData
    {K : Type*} [Field K] [NumberField K]
    (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0 < r) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let qF := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial AlgebraicComplex := fun i => (qF i).map φ
  let qplus := ordinaryReflectionTuple r p
  let d := reciprocalCommonDegree r qplus
  let ν := reciprocalSourceDegree r d qplus
  let A := reciprocalSourceArray r d qplus
  let P := signedLaplaceFirstNuBoundary A a
  0 < ν ∧ P.natDegree ≤ ν-1 ∧ P = 0 ∧
    ∀ k : ℕ, (∑ i, ∑ j, if i.val+k < j.val then
      A i j * (-1:AlgebraicComplex)^(j.val-k-1) *
        (((j.val-k-1).descFactorial i.val):AlgebraicComplex) * a (j.val-i.val-k-1)
      else 0) = 0

theorem selectedFuchsSourceData_firstNu_boundary
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0 < r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ)
    (hpacket : SelectedFuchsSourceData G a φ r hr c T UI E) :
    SelectedFirstNuBoundaryData a φ r hr T UI := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hreg,hpTop,hpReg,
    hplusTop,hplusReg,hdegree,hν,hfuchs,hcorner,hsource,hFourierNonzero,hFourierEq⟩ := hpacket
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    Matrix.of (fun i j => (UI i j).map (algebraMap (𝓞 K) K))
  let qF := sameCompanionScalarTuple r hr t U
  let p : Fin (r+1) → Polynomial AlgebraicComplex := fun i => (qF i).map φ
  let qplus := ordinaryReflectionTuple r p
  let d := reciprocalCommonDegree r qplus
  let ν := reciprocalSourceDegree r d qplus
  let A := reciprocalSourceArray r d qplus
  have hP : signedLaplaceFirstNuBoundary A a = 0 :=
    signedLaplaceFirstNuBoundary_eq_zero_of_source_zero A a hsource
  refine ⟨hν,signedLaplaceFirstNuBoundary_natDegree_le A hν a,hP,?_⟩
  intro k
  have h := congrArg (fun P : Polynomial AlgebraicComplex => P.coeff k) hP
  change (signedLaplaceFirstNuBoundary A a).coeff k = (0 : Polynomial AlgebraicComplex).coeff k at h
  rw [signedLaplaceFirstNuBoundary_coeff_formula, Polynomial.coeff_zero] at h
  exact h

end StrictEUnit
end
