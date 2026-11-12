import OriginalSourceLaurentEulerPresentation

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem originalSource_laurent_unit_forcing_column
    (n : ℕ) (T : Polynomial K) (hT : T≠0) (M : ℕ) (i : Fin (n+1)) :
    laurentIntegerMonomial (((M+T.natTrailingDegree+i.val:ℕ):ℤ)+1-((M+(n+1):ℕ):ℤ))*
      clearedSourceForcingColumn n T i=HahnSeries.ofPowerSeries ℤ K (augmentedSourceEulerColumn n T i) := by
  simp only [clearedSourceForcingColumn,augmentedSourceEulerColumn]
  split_ifs with hi
  · have he : (((M+T.natTrailingDegree+i.val:ℕ):ℤ)+1-((M+(n+1):ℕ):ℤ))=
        (T.natTrailingDegree:ℤ) := by push_cast;omega
    rw [he,originalSource_forcing_unit_tail T hT]
  · rw [mul_zero,map_zero]

/-- Exact source presentation with a constructed common offset, including
negative forcing modes. All matrix coefficients are power series. -/
theorem originalSource_finite_laurent_unit_euler_presentation
    (n : ℕ) (c : Fin (n+1) →RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1))
    (k : ℕ →ℤ) (s : ℕ) :
    let M := finiteLaurentOffset k s
    monomialEulerConnection (finiteLaurentForcingConnection
      (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (clearedSourceForcingColumn n T) k s)
      (finiteLaurentEulerWeights (fun i =>M+T.natTrailingDegree+i.val) (M+(n+1)) k s)=
      (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
        (augmentedSourceEulerColumn n T) (M+(n+1)) k s).map (HahnSeries.ofPowerSeries ℤ K) := by
  intro M
  apply finiteLaurentEulerMatrix_realization
  · rw [monomialEulerConnection_weight_shift,originalSource_monomialEuler_presentation n c T U hT hclear hV]
    funext i j
    simp only [sourceLaurentEulerBase,Matrix.map_apply,Matrix.add_apply,Matrix.diagonal_apply,map_add]
    split_ifs <;> simp [HahnSeries.ofPowerSeries_C]
  · exact originalSource_laurent_unit_forcing_column n T hT M
  · intro j hj
    have h := finiteLaurentOffset_nonnegative k s j hj
    change 0≤((finiteLaurentOffset k s+(n+1):ℕ):ℤ)+k j
    push_cast
    omega

end StrictEUnit
end
