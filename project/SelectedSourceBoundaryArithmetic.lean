import ReciprocalSourceIndicialBoundary
import SelectedSourceRootBinomialArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- Exact SAME selected lower-boundary polynomial and source-root arithmetic
for both origin alternatives. No Fourier spectrum identification is assumed. -/
def SameClearingSourceBoundaryArithmeticData
    {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (φ : K →+* AlgebraicComplex) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let τ := t.coeff t.natTrailingDegree
  let β := polynomialCompanionFace n 1 1 t U
  reciprocalSourceBoundaryIndicial (n+1)
    (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) t U)=
      Polynomial.C τ*regularResidueIndicial n τ β ∧
  ∀ ξ : AlgebraicComplex,
    (regularResidueIndicial n (φ τ) (fun j => φ (β j))).eval ξ=0 →
      BinomialPrefixDenominators ξ

theorem selectedFuchsSourceData_source_boundary_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    SameClearingSourceBoundaryArithmeticData n T UI φ := by
  have harith := selectedFuchsSourceData_source_root_binomial_arithmetic
    G a φ n hr c T UI E hsource
  obtain ⟨hdata,hT,hrest⟩ := hsource
  exact ⟨reciprocalSourceBoundaryIndicial_sameCompanion n _ _ hT,harith⟩

end StrictEUnit
end
