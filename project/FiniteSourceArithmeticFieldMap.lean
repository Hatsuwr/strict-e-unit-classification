import SourceEulerMatrixFieldMap

noncomputable section
open scoped NumberField
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

theorem zeroPaddedPowerSeriesColumn_field_map {r : ℕ} (phi : K →+* L)
    (g : Fin r →PowerSeries K) (s : ℕ) :
    (fun i =>PowerSeries.map phi (zeroPaddedPowerSeriesColumn g s i))=
      zeroPaddedPowerSeriesColumn (fun i =>PowerSeries.map phi (g i)) s := by
  induction s with
  | zero =>rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero =>exact map_zero _
    | succ i =>exact congrFun ih i

theorem finiteLaurentEulerMatrix_field_map {r : ℕ} (phi : K →+* L)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ) (s : ℕ) :
    (finiteLaurentEulerMatrix C g M k s).map (PowerSeries.map phi)=
      finiteLaurentEulerMatrix (C.map (PowerSeries.map phi))
        (fun i =>PowerSeries.map phi (g i)) M k s := by
  induction s with
  | zero =>rfl
  | succ s ih =>
    funext i j
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases <;> simp [finiteLaurentEulerMatrix,forcingEulerBlock,PowerSeries.map_C]
    | succ i =>
      cases j using Fin.cases with
      | zero =>exact congrFun (zeroPaddedPowerSeriesColumn_field_map phi g s) i
      | succ j =>exact congrFun (congrFun ih i) j

theorem actualFiniteSourceMatrix_field_map (phi : K →+* L) (n M H s : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K))
    (hT : T≠0) (k : ℕ →ℤ) :
    (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) H k s).map (PowerSeries.map phi)=
      finiteLaurentEulerMatrix (sourceLaurentEulerBase n (T.map phi) (fun i j =>(U i j).map phi) M)
        (augmentedSourceEulerColumn n (T.map phi)) H k s := by
  rw [finiteLaurentEulerMatrix_field_map,sourceLaurentEulerBase_field_map phi n M T U hT]
  have hg : (fun i =>PowerSeries.map phi (augmentedSourceEulerColumn n T i))=
      augmentedSourceEulerColumn n (T.map phi) :=
    funext (fun i =>augmentedSourceEulerColumn_field_map phi n T hT i)
  rw [hg]

/-- Original source arithmetic extends to the exact enlarged-field regular
source/forcing matrix, with the same denominator integers and growth bound. -/
theorem selectedFuchsSourceData_extended_finite_source_arithmetic
    [NumberField K] (psi : K →+* L)
    (G : PowerSeries K) (a : ℕ →AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (n : ℕ) (hr : 0<n+1) (c : Fin (n+1) →RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi (n+1) hr c T UI E)
    (k : ℕ →ℤ) (s : ℕ) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=fun i j =>(UI i j).map (algebraMap (𝓞 K) K)
    let M := finiteLaurentOffset k s
    RegularEulerPrefixArithmetic (finiteLaurentEulerMatrix
      (sourceLaurentEulerBase n (t.map psi) (fun i j =>(U i j).map psi) M)
      (augmentedSourceEulerColumn n (t.map psi)) (M+(n+1)) k s) := by
  intro t U M
  have hC := selectedFuchsSourceData_finite_laurent_unit_euler_arithmetic G a phi n hr c T UI E hsource k s
  have hm := RegularEulerPrefixArithmetic.field_map hC psi
  obtain ⟨hdata,hT,hrest⟩ := hsource
  rwa [actualFiniteSourceMatrix_field_map psi n M (M+(n+1)) s t U hT k] at hm

end StrictEUnit
end
