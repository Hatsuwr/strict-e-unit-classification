import IndicialBinomialRootTransfer
import SelectedIndicialRootArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- At the ordinary original center every guarded lower residue coefficient
vanishes, so the source indicial polynomial is the literal falling polynomial. -/
theorem polynomialCompanionFace_ordinary_zero
    {K : Type*} [Field K] (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (ht : T.natTrailingDegree=0) (j : Fin (n+1)) :
    polynomialCompanionFace n 1 1 T U j=0 := by
  have hj := j.isLt
  simp only [polynomialCompanionFace,ht,Nat.one_mul,Nat.mul_one]
  rw [if_neg (by omega)]

theorem regularResidueIndicial_ordinary_eq_desc
    {K L : Type*} [Field K] [Field L] (φ : K →+* L)
    (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (ht : T.natTrailingDegree=0) :
    regularResidueIndicial n (φ (T.coeff T.natTrailingDegree))
      (fun j => φ (polynomialCompanionFace n 1 1 T U j))=descPochhammer L (n+1) := by
  simp only [regularResidueIndicial,polynomialCompanionFace_ordinary_zero n T U ht,
    map_zero,zero_div,Polynomial.C_0,zero_mul,Finset.sum_const_zero,sub_zero]

/-- Actual source-root arithmetic for BOTH original-center alternatives.
The ordinary branch is discharged by its derived integer roots, and the
singular branch uses the original common-denominator theorem. No positive
trailing order or rational-spectrum input is supplied. -/
theorem selectedFuchsSourceData_source_root_binomial_arithmetic
    {K : Type*} [Field K] [NumberField K]
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (φ : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a φ (n+1) hr c T UI E) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
      fun i j => (UI i j).map (algebraMap (𝓞 K) K)
    ∀ ξ : AlgebraicComplex,
      (regularResidueIndicial n (φ (t.coeff t.natTrailingDegree))
        (fun j => φ (polynomialCompanionFace n 1 1 t U j))).eval ξ=0 →
      BinomialPrefixDenominators ξ := by
  intro t U ξ hξ
  by_cases ht : t.natTrailingDegree=0
  · rw [regularResidueIndicial_ordinary_eq_desc φ n t U ht] at hξ
    obtain ⟨k,hk,hcast⟩ := (descPochhammer_eval_eq_zero_iff_natCast (n+1) ξ).1 hξ
    rw [hcast]
    exact natCast_binomialPrefixDenominators k
  · obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
    exact same_clearing_algebraicComplex_indicial_binomial_denominators
      φ n c T UI hT hclear E hE hden (Nat.pos_of_ne_zero ht) ξ hξ

end StrictEUnit
end
