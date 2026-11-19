import FrobeniusFullCoefficientRealization

/-! Literal Laurent coefficient operator and integer-shift transport.
The input is any LaurentSeries (Polynomial K), with no uniform log bound. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

def laurentCoefficientShift (k : ℤ) (s : LaurentSeries (Polynomial K)) :
    LaurentSeries (Polynomial K) := HahnSeries.single k 1 * s

theorem laurentCoefficientShift_coeff (k n : ℤ) (s : LaurentSeries (Polynomial K)) :
    (laurentCoefficientShift k s).coeff n = s.coeff (n-k) := by
  have h := HahnSeries.coeff_single_mul_add (r := (1 : Polynomial K))
    (x := s) (a := n-k) (b := k)
  simpa only [laurentCoefficientShift,sub_add_cancel,one_mul] using h

theorem laurentCoefficientShift_injective (k : ℤ) :
    Function.Injective (laurentCoefficientShift (K := K) k) := by
  intro s t h
  apply HahnSeries.ext
  funext n
  have hc := congrArg (fun v : LaurentSeries (Polynomial K) => v.coeff (n+k)) h
  simpa only [laurentCoefficientShift_coeff,add_sub_cancel_right] using hc

theorem logPolynomialToCoefficientSeries_integerShift (k : ℤ)
    (p : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (frobeniusIntegerShift k p) =
      laurentCoefficientShift k (logPolynomialToCoefficientSeries p) := by
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro j
  rw [logPolynomialToCoefficientSeries_double_coeff,frobeniusIntegerShift_coeff,
    laurentCoefficientShift_coeff,logPolynomialToCoefficientSeries_double_coeff]

def scalarTwistedCoefficientOperator (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (ξ : K) (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) :=
  ∑ i : Fin (r+1),logLaurentCoefficientMap (b i : LaurentSeries K) *
    (twistedPolynomialCoefficientEuler ξ)^[i.val] s

theorem logPolynomialToCoefficientSeries_scalarTwistedCoefficientOperator
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K)
    (p : Polynomial (LaurentSeries K)) :
    logPolynomialToCoefficientSeries (scalarTwistedLogOperator r b ξ p) =
      scalarTwistedCoefficientOperator r b ξ (logPolynomialToCoefficientSeries p) := by
  simp only [scalarTwistedLogOperator,scalarTwistedCoefficientOperator,map_sum,map_mul,
    logPolynomialToCoefficientSeries_C,logPolynomialToCoefficientSeries_twistedEuler_iterate]

theorem laurentCoefficientShift_twistedEuler (ξ : K) (k : ℤ)
    (s : LaurentSeries (Polynomial K)) :
    twistedPolynomialCoefficientEuler ξ (laurentCoefficientShift k s) =
      laurentCoefficientShift k (twistedPolynomialCoefficientEuler (ξ + (k : K)) s) := by
  apply HahnSeries.ext
  funext n
  simp only [twistedPolynomialCoefficientEuler_coeff,laurentCoefficientShift_coeff,Int.cast_sub]
  congr 2
  ring

theorem laurentCoefficientShift_twistedEuler_iterate (ξ : K) (k : ℤ)
    (s : LaurentSeries (Polynomial K)) (i : ℕ) :
    (twistedPolynomialCoefficientEuler ξ)^[i] (laurentCoefficientShift k s) =
      laurentCoefficientShift k ((twistedPolynomialCoefficientEuler (ξ + (k : K)))^[i] s) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih,laurentCoefficientShift_twistedEuler,
      Function.iterate_succ_apply']

theorem laurentCoefficientShift_scalarTwistedCoefficientOperator
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) (k : ℤ)
    (s : LaurentSeries (Polynomial K)) :
    scalarTwistedCoefficientOperator r b ξ (laurentCoefficientShift k s) =
      laurentCoefficientShift k (scalarTwistedCoefficientOperator r b (ξ+(k : K)) s) := by
  unfold scalarTwistedCoefficientOperator
  simp_rw [laurentCoefficientShift_twistedEuler_iterate]
  simp only [laurentCoefficientShift,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- This transport holds for every power-series coefficient sequence, even
before any logarithmic bound or polynomial-log realization is known. -/
theorem scalarTwistedCoefficientOperator_powerSeries
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) (u : ℕ → Polynomial K) :
    scalarTwistedCoefficientOperator r b ξ
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) =
      (polynomialLogPowerSeriesOperator r b ξ u : LaurentSeries (Polynomial K)) := by
  have hit (i : ℕ) : (twistedPolynomialCoefficientEuler ξ)^[i]
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) =
      ((PowerSeries.mk (fun n => (shiftedPolynomialDerivative (ξ + (n : K)))^[i] (u n)) :
        PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) := by
    apply HahnSeries.ext
    funext n
    rw [twistedPolynomialCoefficientEuler_iterate_coeff]
    cases n with
    | ofNat n =>
      simp only [Int.ofNat_eq_coe,LaurentSeries.coeff_coe_powerSeries,
        PowerSeries.coeff_mk,Int.cast_natCast]
    | negSucc n =>
      simp only [PowerSeries.coeff_coe,Int.negSucc_lt_zero,if_true,iterate_map_zero]
  unfold scalarTwistedCoefficientOperator polynomialLogPowerSeriesOperator
  simp only [hit,logLaurentCoefficientMap_powerSeries,PowerSeries.coe_mul,map_sum]

theorem scalarTwistedCoefficientOperator_powerSeries_eq_zero_iff
    (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) (u : ℕ → Polynomial K) :
    scalarTwistedCoefficientOperator r b ξ
      ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K)) = 0 ↔
      ∀ n,polynomialLogEulerCoefficient
        (scalarEulerCoefficientSymbol r (fun i k => PowerSeries.coeff K k (b i))) ξ u n = 0 := by
  rw [scalarTwistedCoefficientOperator_powerSeries]
  constructor
  · intro h n
    have hc := congrArg (fun s : LaurentSeries (Polynomial K) => s.coeff (n : ℤ)) h
    simpa only [LaurentSeries.coeff_coe_powerSeries,polynomialLogPowerSeriesOperator_coeff,
      HahnSeries.coeff_zero] using hc
  · intro h
    have hz : polynomialLogPowerSeriesOperator r b ξ u = 0 := by
      apply PowerSeries.ext
      intro n
      rw [polynomialLogPowerSeriesOperator_coeff,h n,map_zero]
    rw [hz,PowerSeries.coe_zero]

end StrictEUnit
end

#print axioms StrictEUnit.laurentCoefficientShift_coeff
#print axioms StrictEUnit.laurentCoefficientShift_injective
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_integerShift
#print axioms StrictEUnit.logPolynomialToCoefficientSeries_scalarTwistedCoefficientOperator
#print axioms StrictEUnit.laurentCoefficientShift_twistedEuler
#print axioms StrictEUnit.laurentCoefficientShift_twistedEuler_iterate
#print axioms StrictEUnit.laurentCoefficientShift_scalarTwistedCoefficientOperator
#print axioms StrictEUnit.scalarTwistedCoefficientOperator_powerSeries
#print axioms StrictEUnit.scalarTwistedCoefficientOperator_powerSeries_eq_zero_iff
