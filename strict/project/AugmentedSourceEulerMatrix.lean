import FiniteForcingEulerPresentation
import SameCompanionEulerGaugeConnection

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- The original source companion has its previously proved regular Euler
presentation; this is an exact matrix identification. -/
theorem originalSource_monomialEuler_presentation
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1)) :
    monomialEulerConnection
      (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (fun i =>i.val)=(sameCompanionEulerPowerSeriesMatrix n T U).map (HahnSeries.ofPowerSeries ℤ K) := by
  have h := same_companion_euler_gauge_matrix n c T U hT hclear hV
  rw [monomialEulerConnection_gauge] at h
  funext i j
  apply mul_left_cancel₀ (laurentIntegerMonomial_ne_zero (K:=K) (-1))
  exact congrFun (congrFun h i) j

/-- A common shift by ord_0 T makes ALL source and forcing weights natural. -/
def augmentedSourceEulerBase (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) :
    Matrix (Fin (n+1)) (Fin (n+1)) (PowerSeries K) :=
  sameCompanionEulerPowerSeriesMatrix n T U+
    Matrix.diagonal (fun _ =>PowerSeries.C K (T.natTrailingDegree : K))

def clearedSourceForcingColumn (n : ℕ) (T : Polynomial K) : Fin (n+1) →LaurentSeries K :=
  fun i =>if i.val+1=n+1 then (polynomialLaurentImage T)⁻¹ else 0

def augmentedSourceEulerColumn (n : ℕ) (T : Polynomial K) : Fin (n+1) →PowerSeries K :=
  fun i =>if i.val+1=n+1 then (sameCompanionEulerDenominatorSeries T)⁻¹ else 0

def augmentedSourceEulerWeights (n : ℕ) (T : Polynomial K) (d : ℕ) :
    Fin (((n+1)+1)+d) →ℕ :=
  polynomialForcingEulerWeights (fun i : Fin (n+1) =>T.natTrailingDegree+i.val) (n+1) d

def augmentedSourceEulerMatrix (n : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (d : ℕ) :
    Matrix (Fin (((n+1)+1)+d)) (Fin (((n+1)+1)+d)) (PowerSeries K) :=
  polynomialForcingEulerMatrix (augmentedSourceEulerBase n T U)
    (augmentedSourceEulerColumn n T) (n+1) d

/-- The forcing pole cancels against the chosen integer monomial, leaving
only the reciprocal of the ACTUAL nonzero-constant tail of the original T. -/
theorem originalSource_forcing_unit_tail (T : Polynomial K) (hT : T≠0) :
    laurentIntegerMonomial (T.natTrailingDegree : ℤ)*(polynomialLaurentImage T)⁻¹=
      HahnSeries.ofPowerSeries ℤ K ((sameCompanionEulerDenominatorSeries T)⁻¹) := by
  let psi := HahnSeries.ofPowerSeries ℤ K
  have hf : polynomialLaurentImage T=laurentIntegerMonomial (T.natTrailingDegree : ℤ)*
      psi (sameCompanionEulerDenominatorSeries T) := by
    have h := congrArg psi (sameCompanionEulerDenominatorSeries_factor T)
    simpa only [map_mul,HahnSeries.ofPowerSeries_X_pow,polynomialLaurentImage,psi,laurentIntegerMonomial] using h.symm
  apply mul_right_cancel₀ (polynomialLaurentImage_ne_zero T hT)
  rw [mul_assoc,inv_mul_cancel₀ (polynomialLaurentImage_ne_zero T hT),mul_one,hf]
  rw [mul_left_comm,← map_mul,PowerSeries.inv_mul_cancel _
    (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT),map_one,mul_one]

/-- Exact regular Euler realization of EVERY augmented SOURCE forcing matrix.
The source order, original clearing tuple and all forcing coordinates survive.
No Fourier connection is substituted. -/
theorem augmentedSourceEulerMatrix_realization
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1)) (d : ℕ) :
    monomialEulerConnection (polynomialForcingConnection
      (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (clearedSourceForcingColumn n T) d) (augmentedSourceEulerWeights n T d)=
      (augmentedSourceEulerMatrix n T U d).map (HahnSeries.ofPowerSeries ℤ K) := by
  apply polynomialForcingEulerMatrix_realization
  · rw [monomialEulerConnection_weight_shift,originalSource_monomialEuler_presentation n c T U hT hclear hV]
    funext i j
    simp only [augmentedSourceEulerBase,Matrix.map_apply,Matrix.add_apply,Matrix.diagonal_apply,map_add]
    split_ifs <;> simp [HahnSeries.ofPowerSeries_C]
  · intro i
    simp only [clearedSourceForcingColumn,augmentedSourceEulerColumn]
    split_ifs with hi
    · have he : ((T.natTrailingDegree+i.val : ℕ) : ℤ)+1-((n+1 : ℕ) : ℤ)=(T.natTrailingDegree : ℤ) := by
        push_cast
        omega
      rw [he]
      exact originalSource_forcing_unit_tail T hT
    · rw [mul_zero,map_zero]

end StrictEUnit
end
