import CyclicRegularEulerFrame
import CyclicJetInverseTriangular
import SelectedAugmentedSourceEulerArithmetic

noncomputable section
open scoped BigOperators Classical Matrix NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The SAME augmented source admits a constructed monic scalar equation and,
when its actual indicial polynomial splits, a constructed logarithmic frame.
The scalar equation is not identified with a Fourier equation. -/
theorem augmentedSourceEuler_constructed_frame (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) (d : ℕ) :
    ∃ b : Fin ((((n+1)+1)+d)+1) →PowerSeries K,
      b (Fin.last (((n+1)+1)+d))=1 ∧
      ∀ hsplit : (scalarEulerCoefficientSymbol (((n+1)+1)+d)
        (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K),
      ∃ rho : Fin (((n+1)+1)+d) →K,
      ∃ Y : Matrix (Fin (((n+1)+1)+d)) (Fin (((n+1)+1)+d)) (Polynomial (LaurentSeries K)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding (augmentedSourceEulerMatrix n T U d i l)*Y l j) := by
  let C := augmentedSourceEulerMatrix n T U d
  let e := forcingCoordinateEquiv (n+1) d
  have hC : EulerCyclicShape (C.submatrix e e) :=
    augmentedSourceEulerMatrix_ordered_cyclicShape n T U hT d
  obtain ⟨b,G,H,hb,hdet,hGH,hHG,hconn⟩ := cyclicShape_exists_scalarGauge (C.submatrix e e) (by omega) hC
  refine ⟨b,hb,fun hsplit =>?_⟩
  have htop : PowerSeries.constantCoeff K (b (Fin.last (((n+1)+1)+d)))≠0 := by rw [hb,map_one];exact one_ne_zero
  obtain ⟨rho,Y,hYdet,hY⟩ := regularScalarGauge_constructed_log_frame (C.submatrix e e) b G H
    htop hGH hHG hconn hsplit
  refine ⟨fun j =>rho (e.symm j),Y.submatrix e.symm e.symm,?_,?_⟩
  · simpa only [Matrix.det_submatrix_equiv_self] using hYdet
  · have h := regularEuler_log_frame_reindex (C.submatrix e e) rho Y hY e.symm
    simpa only [Matrix.submatrix,Matrix.of_apply,Equiv.apply_symm_apply,C] using h

def AugmentedSourceScalarFrameData (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) : Prop :=
  ∀ d : ℕ,∃ b : Fin ((((n+1)+1)+d)+1) →PowerSeries K,
    b (Fin.last (((n+1)+1)+d))=1 ∧
    ∀ hsplit : (scalarEulerCoefficientSymbol (((n+1)+1)+d)
      (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K),
    ∃ rho : Fin (((n+1)+1)+d) →K,
    ∃ Y : Matrix (Fin (((n+1)+1)+d)) (Fin (((n+1)+1)+d)) (Polynomial (LaurentSeries K)),
      Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
        ∑ l,logPowerSeriesEmbedding (augmentedSourceEulerMatrix n T U d i l)*Y l j)

/-- The original source hypotheses now supply the scalar/frame construction.
Splitting is exposed rather than silently changing fields. -/
theorem selectedFuchsSourceData_augmented_constructed_frame [NumberField K]
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E) :
    AugmentedSourceScalarFrameData n (T.map (algebraMap (𝓞 K) K))
      (fun i j =>(UI i j).map (algebraMap (𝓞 K) K)) := by
  obtain ⟨hdata,hT,hrest⟩ := hsource
  intro d
  exact augmentedSourceEuler_constructed_frame n _ _ hT d

end StrictEUnit
end
