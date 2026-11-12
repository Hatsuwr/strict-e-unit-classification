import FiniteSourceArithmeticFieldMap

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L]

/-- The original source supplies an arithmetic frame over every enlarged
number field, for the exact mapped source and the finite actual residual
extension. No extension of minimality or of the entire source packet is needed. -/
theorem selectedFuchsSourceData_extended_residual_frame
    (psi : K →+* L)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (d s : ℕ) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
    let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
    let M := finiteLaurentOffset k (s+1)
    FiniteSplittingUnfilteredFrameData (finiteLaurentEulerMatrix
      (sourceLaurentEulerBase n (t.map psi) (fun i j =>(U i j).map psi) M)
      (augmentedSourceEulerColumn n (t.map psi)) (M+(n+1)) k (s+1)) := by
  intro t U k M
  have hC := selectedFuchsSourceData_extended_finite_source_arithmetic psi G a phi n hr c T UI E hsource k (s+1)
  obtain ⟨hdata,hT,hrest⟩ := hsource
  have hT' : t.map psi≠0 := (Polynomial.map_ne_zero_iff psi.injective).mpr hT
  apply actualFiniteLaurentSource_unfiltered_frame n s M (M+(n+1)) (t.map psi)
    (fun i j =>(U i j).map psi) hT' k _ hC
  have hi := shiftedResidualEigenvalues_injective (K:=L) (s+1) ((M+(n+1):ℕ):ℤ) (d:ℤ)
  convert hi using 1
  funext j
  dsimp [k]
  push_cast
  ring

end StrictEUnit
end
