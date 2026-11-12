import AlignedActualFrameArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A finite splitting field with full unfiltered arithmetic of an actual
logarithmic source frame. Integer alignment has already been constructed. -/
def FiniteSplittingUnfilteredFrameData {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Prop :=
  ∃ b : Fin (r+1) →PowerSeries K,b (Fin.last r)=1 ∧
    let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
    let L := P.SplittingField
    ∃ hNF : NumberField L,FiniteDimensional K L ∧
      ∃ rho : Fin r →L,∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries L)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding ((C.map (PowerSeries.map (algebraMap K L))) i l)*Y l j) ∧
        JointBinomialPrefixDenominators rho ∧
        ∃ A : ℤ,∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,
          0<D ∧ (D : ℝ)≤B^(N+1) ∧ ∀ m,m≤N →∀ s i j,
          IsIntegral ℤ ((D : L)*((Y i s).coeff j).coeff ((m : ℤ)+A))

theorem finiteSplittingArithmeticFrame_unfiltered {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hC : RegularEulerPrefixArithmetic C) (hf : FiniteSplittingArithmeticFrameData C) :
    FiniteSplittingUnfilteredFrameData C := by
  obtain ⟨b,hb,hNF,hfd,rho,Y,hdet,hY,hrho,hfiltered⟩ := hf
  letI := hNF
  letI := hfd
  obtain ⟨rep,shift,hs,hd,he,ha⟩ := actualLogFrame_exists_aligned_arithmetic
    _ (hC.field_map _) rho hrho Y hY hdet
  exact ⟨b,hb,hNF,hfd,rho ∘ rep,_,hd,he,hrho.comp rep,ha⟩

end StrictEUnit
end
