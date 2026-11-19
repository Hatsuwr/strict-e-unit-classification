import RegularScalarGaugeFieldTransport

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Both the actual frame and its exponent arithmetic are constructed from the
regular source connection and its proved scalar gauge. Only splitting remains. -/
theorem regularScalarGauge_constructed_arithmetic_frame {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r) (hC : RegularEulerPrefixArithmetic C)
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K)) :
    ∃ rho : Fin r →K,∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries K)),
      Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
        ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) ∧ JointBinomialPrefixDenominators rho := by
  have htop : PowerSeries.constantCoeff K (b (Fin.last r))≠0 := by rw [hb,map_one];exact one_ne_zero
  let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
  let e := scalarEulerFrobeniusIndexEquiv r b htop hsplit
  let rho : Fin r →K := fun j =>frobeniusRootSeedExponent (B 0) (e.symm j)
  let Z := frobeniusActualJetMatrix B e
  obtain ⟨hdet,hZ,hJ⟩ := scalarEuler_constructed_frobenius_frame r b htop hsplit
  obtain ⟨hYdet,hY⟩ := regularEuler_log_frame_pullback C _ G H hGH hHG hc rho Z hZ hdet
  refine ⟨rho,H.map logPowerSeriesEmbedding*Z,hYdet,hY,?_⟩
  apply finite_binomialPrefixDenominators rho
  intro j
  apply regularScalarGauge_indicial_binomial C hr hC b hb G H hGH hHG hc (rho j)
  exact frobeniusRootSeedExponent_isRoot (B 0) (e.symm j)

/-- A finite splitting field removes the splitting premise. The coefficient
map, actual source matrix, denominator integers, scalar gauge and exponents
are all transported explicitly. No unfiltered arithmetic is asserted. -/
theorem regularScalarGauge_finite_splitting_arithmetic_frame {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r) (hC : RegularEulerPrefixArithmetic C)
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G) :
    let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
    let L := P.SplittingField
    ∃ hNF : NumberField L,
      ∃ rho : Fin r →L,∃ Y : Matrix (Fin r) (Fin r) (Polynomial (LaurentSeries L)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding ((C.map (PowerSeries.map (algebraMap K L))) i l)*Y l j) ∧
        JointBinomialPrefixDenominators rho := by
  dsimp only
  let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
  let L := P.SplittingField
  obtain ⟨hNF,hsplit⟩ := scalarIndicial_finite_splitting_field b
  letI : NumberField L := hNF
  let phi := algebraMap K L
  have hb' : PowerSeries.map phi (b (Fin.last r))=1 := by rw [hb,map_one]
  obtain ⟨hGH',hHG',hc'⟩ := monicScalarGauge_field_map phi C G H b hb hGH hHG hc
  exact ⟨hNF,regularScalarGauge_constructed_arithmetic_frame
    (C.map (PowerSeries.map phi)) hr (hC.field_map phi)
    (fun i =>PowerSeries.map phi (b i)) hb' (G.map (PowerSeries.map phi))
    (H.map (PowerSeries.map phi)) hGH' hHG' hc' hsplit⟩

end StrictEUnit
end
