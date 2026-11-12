import ActualFiniteLaurentScalarGauge

noncomputable section
open scoped BigOperators Classical Matrix NumberField
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The scalar gauge and original connection arithmetic produce a finite
splitting field, an actual frame, and joint exponent/filtered arithmetic. -/
theorem regularScalarGauge_finite_arithmetic_data {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (hr : 0<r)
    (hC : RegularEulerPrefixArithmetic C)
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1)
    (G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G) :
    FiniteSplittingArithmeticFrameData C := by
  refine ⟨b,hb,?_⟩
  let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
  let L := P.SplittingField
  obtain ⟨hNF,rho,Y,hdet,hY,hrho⟩ := regularScalarGauge_finite_splitting_arithmetic_frame
    C hr hC b hb G H hGH hHG hc
  letI : NumberField L := hNF
  obtain ⟨B,hB,hden⟩ := hC.field_map (algebraMap K L)
  exact ⟨hNF,inferInstance,rho,Y,hdet,hY,hrho,
    logFrame_filtered_solution_common_denominators _ B hB hden rho hrho Y hY hdet⟩

/-- Full unfiltered frame arithmetic for the actual extension, with splitting
and exponent arithmetic derived rather than postulated. -/
theorem actualFiniteLaurentSource_unfiltered_frame
    (n s M L : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (k : ℕ →ℤ)
    (hinj : Function.Injective (fun j : Fin (s+1) =>(((L:ℤ)+k j.val):K)))
    (hC : RegularEulerPrefixArithmetic (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) L k (s+1))) :
    FiniteSplittingUnfilteredFrameData (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) L k (s+1)) := by
  obtain ⟨b,G,H,hb,hGH,hHG,hc⟩ := actualFiniteLaurentSource_scalarGauge n s M L T U hT k hinj
  exact finiteSplittingArithmeticFrame_unfiltered _ hC
    (regularScalarGauge_finite_arithmetic_data _ (by omega) hC b hb G H hGH hHG hc)

/-- Original selected-source hypotheses supply every premise for actual
residual-extension frame arithmetic. No new splitting or frame assumption. -/
theorem selectedFuchsSourceData_actual_residual_unfiltered_frame
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (d s : ℕ) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
    let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
    let M := finiteLaurentOffset k (s+1)
    FiniteSplittingUnfilteredFrameData (finiteLaurentEulerMatrix (sourceLaurentEulerBase n t U M)
      (augmentedSourceEulerColumn n t) (M+(n+1)) k (s+1)) := by
  intro t U k M
  have hC := selectedFuchsSourceData_finite_laurent_unit_euler_arithmetic G a phi n hr c T UI E hsource k (s+1)
  obtain ⟨hdata,hT,hrest⟩ := hsource
  apply actualFiniteLaurentSource_unfiltered_frame n s M (M+(n+1)) t U hT k _ hC
  have hi := shiftedResidualEigenvalues_injective (K:=K) (s+1) ((M+(n+1):ℕ):ℤ) (d:ℤ)
  convert hi using 1
  funext j
  dsimp [k]
  push_cast
  ring

end StrictEUnit
end
