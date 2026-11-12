import ScalarGaugeConstructedArithmeticFrame
import LogFrameFilteredDenominators

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- Reindexing a family changes neither denominator integers nor their bound. -/
theorem JointBinomialPrefixDenominators.comp {K ι κ : Type*} [Field K]
    {rho : ι →K} (hrho : JointBinomialPrefixDenominators rho) (f : κ →ι) :
    JointBinomialPrefixDenominators (rho ∘ f) := by
  obtain ⟨B,hB,hden⟩ := hrho
  refine ⟨B,hB,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  exact ⟨D,hD,hDb,fun m hm j =>hDi m hm (f j)⟩

variable {K : Type*} [Field K] [NumberField K]

/-- A precise finite-extension result. All geometry and exponent arithmetic are
conclusions; coefficient arithmetic is still filtered, not the full sequence. -/
def FiniteSplittingArithmeticFrameData {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Prop :=
  ∃ b : Fin (r+1) →PowerSeries K,b (Fin.last r)=1 ∧
    let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
    let L := P.SplittingField
    ∃ hNF : NumberField L,FiniteDimensional K L ∧
      ∃ rho : Fin r →L,∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries L)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding ((C.map (PowerSeries.map (algebraMap K L))) i l)*Y l j) ∧
        JointBinomialPrefixDenominators rho ∧
        ∃ A : ℤ,∃ q : ℕ,∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,
          0<D ∧ (D : ℝ)≤B^(N+1) ∧ ∀ m,m≤N →∀ s i j,
          IsIntegral ℤ ((D : L)*((literalLogPolynomialFilter (rho s)
            (allClassPrefixFilter rho A m q) (Y i s)).coeff j).coeff ((m : ℤ)+A))

/-- A positive system with actual regular connection arithmetic and the
proved cyclic shape after a coordinate permutation has a finite-extension
arithmetic frame. Splitting and binomial arithmetic are DERIVED, not premises. -/
theorem regularEuler_cyclic_permutation_arithmetic_frame {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r)
    (hC : RegularEulerPrefixArithmetic C) (e : Equiv.Perm (Fin r))
    (hshape : EulerCyclicShape (C.submatrix e e)) : FiniteSplittingArithmeticFrameData C := by
  obtain ⟨b,G,H,hb,hdetG,hGH,hHG,hconn⟩ := cyclicShape_exists_scalarGauge (C.submatrix e e) hr hshape
  refine ⟨b,hb,?_⟩
  let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
  let L := P.SplittingField
  obtain ⟨hNF,rho,Y,hdet,hY,hrho⟩ := regularScalarGauge_finite_splitting_arithmetic_frame
    (C.submatrix e e) hr (hC.reindex e) b hb G H hGH hHG hconn
  letI : NumberField L := hNF
  let Y' := Y.submatrix e.symm e.symm
  let rho' := rho ∘ e.symm
  have hdet' : Y'.det≠0 := by simpa only [Y',Matrix.det_submatrix_equiv_self] using hdet
  have hY' : ∀ j i,twistedLogPolynomialEuler (rho' j) (Y' i j)=
      ∑ l,logPowerSeriesEmbedding ((C.map (PowerSeries.map (algebraMap K L))) i l)*Y' l j := by
    have h := regularEuler_log_frame_reindex
      ((C.submatrix e e).map (PowerSeries.map (algebraMap K L))) rho Y hY e.symm
    simpa only [Y',rho',Function.comp_apply,Matrix.submatrix,Matrix.of_apply,
      Matrix.map_apply,Equiv.apply_symm_apply] using h
  have hrho' : JointBinomialPrefixDenominators rho' := hrho.comp e.symm
  obtain ⟨B,hB,hden⟩ := hC.field_map (algebraMap K L)
  exact ⟨hNF,inferInstance,rho',Y',hdet',hY',hrho',
    logFrame_filtered_solution_common_denominators _ B hB hden rho' hrho' Y' hY' hdet'⟩

end StrictEUnit
end
