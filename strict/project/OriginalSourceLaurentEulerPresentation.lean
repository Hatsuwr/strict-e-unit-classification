import FiniteLaurentEulerPresentation
import AugmentedSourceEulerMatrix

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def finiteLaurentOffset (k : ℕ →ℤ) (s : ℕ) : ℕ := ∑ j ∈ Finset.range s,(k j).natAbs

theorem finiteLaurentOffset_nonnegative (k : ℕ →ℤ) (s j : ℕ) (hj : j<s) :
    0≤(finiteLaurentOffset k s:ℤ)+k j := by
  have hle : (k j).natAbs≤finiteLaurentOffset k s := by
    unfold finiteLaurentOffset
    exact Finset.single_le_sum (fun i hi =>Nat.zero_le ((k i).natAbs)) (Finset.mem_range.mpr hj)
  have hneg : -((k j).natAbs:ℤ)≤k j := by
    rw [Int.natCast_natAbs]
    exact neg_abs_le _
  omega

def sourceLaurentEulerBase (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (M : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K) :=
  sameCompanionEulerPowerSeriesMatrix n T U+
    Matrix.diagonal (fun _ =>PowerSeries.C K ((M+T.natTrailingDegree:ℕ):K))

def sourceLaurentEulerColumn (n : ℕ) (T : Polynomial K) : Fin (n+1) →PowerSeries K :=
  fun i =>if i.val+1=n+1 then PowerSeries.X^(n+1)*(sameCompanionEulerDenominatorSeries T)⁻¹ else 0

theorem originalSource_laurent_forcing_column
    (n : ℕ) (T : Polynomial K) (hT : T≠0) (M : ℕ) (i : Fin (n+1)) :
    laurentIntegerMonomial (((M+T.natTrailingDegree+i.val:ℕ):ℤ)+1-(M:ℤ))*
      clearedSourceForcingColumn n T i=HahnSeries.ofPowerSeries ℤ K (sourceLaurentEulerColumn n T i) := by
  simp only [clearedSourceForcingColumn,sourceLaurentEulerColumn]
  split_ifs with hi
  · have he : (((M+T.natTrailingDegree+i.val:ℕ):ℤ)+1-(M:ℤ))=
        ((n+1:ℕ):ℤ)+(T.natTrailingDegree:ℤ) := by push_cast;omega
    rw [he,← laurentIntegerMonomial_mul,mul_assoc,originalSource_forcing_unit_tail T hT,map_mul,map_pow]
    congr 1
    simp only [HahnSeries.ofPowerSeries_X,laurentIntegerMonomial,HahnSeries.single_pow,one_pow,nsmul_eq_mul,mul_one]
  · rw [mul_zero,map_zero]

/-- Exact source presentation with a constructed common offset, including
negative forcing modes. All matrix coefficients are power series. -/
theorem originalSource_finite_laurent_euler_presentation
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
      (finiteLaurentEulerWeights (fun i =>M+T.natTrailingDegree+i.val) M k s)=
      (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
        (sourceLaurentEulerColumn n T) M k s).map (HahnSeries.ofPowerSeries ℤ K) := by
  intro M
  apply finiteLaurentEulerMatrix_realization
  · rw [monomialEulerConnection_weight_shift,originalSource_monomialEuler_presentation n c T U hT hclear hV]
    funext i j
    simp only [sourceLaurentEulerBase,Matrix.map_apply,Matrix.add_apply,Matrix.diagonal_apply,map_add]
    split_ifs <;> simp [HahnSeries.ofPowerSeries_C]
  · exact originalSource_laurent_forcing_column n T hT M
  · exact fun j hj =>finiteLaurentOffset_nonnegative k s j hj

end StrictEUnit
end
