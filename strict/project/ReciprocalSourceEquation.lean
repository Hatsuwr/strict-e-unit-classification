import ReciprocalGaugeLaurent
import ReciprocalSourceArray
import SignedLaplaceFourierAttachment

/-! NEW SOURCE-ONLY, UNCOMPILED. Explicit nonzero source equation from the
same ordinary tuple. Nonzero array is NOT a nonzero last corner or Fuchs support. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def reciprocalGaugeW : LaurentSeries K := HahnSeries.single (1 : ℤ) (1 : K)

theorem reciprocalGauge_inverse :
    reciprocalGaugeZ (K := K) * reciprocalGaugeW = 1 := by
  unfold reciprocalGaugeZ reciprocalGaugeW
  rw [HahnSeries.single_mul_single]
  norm_num only [one_mul, HahnSeries.single_zero_one]

theorem reciprocalGauge_reflect_eval (d : ℕ) (q : Polynomial K) (hd : q.natDegree ≤ d) :
    Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d q) =
      (reciprocalGaugeZ (K := K))^d * Polynomial.aeval reciprocalGaugeW q := by
  letI : Invertible (reciprocalGaugeW (K := K)) := {
    invOf := reciprocalGaugeZ
    invOf_mul_self := reciprocalGauge_inverse
    mul_invOf_self := by rw [mul_comm]; exact reciprocalGauge_inverse }
  have h := Polynomial.eval₂_reflect_mul_pow
    (algebraMap K (LaurentSeries K)) (reciprocalGaugeW (K := K)) d q hd
  change Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d q) *
    (reciprocalGaugeW (K := K))^d = Polynomial.aeval reciprocalGaugeW q at h
  rw [← h]
  have hpow : (reciprocalGaugeZ (K := K))^d * reciprocalGaugeW^d = 1 := by
    rw [← mul_pow, reciprocalGauge_inverse, one_pow]
  calc
    _ = ((reciprocalGaugeZ (K := K))^d * reciprocalGaugeW^d) *
        Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d q) := by rw [hpow, one_mul]
    _ = _ := by ring

theorem reciprocalGauge_aevalW (q : Polynomial K) :
    Polynomial.aeval (reciprocalGaugeW (K := K)) q =
      HahnSeries.ofPowerSeries ℤ K (q : PowerSeries K) := by
  induction q using Polynomial.induction_on with
  | C c =>
    simp only [Polynomial.aeval_C, Polynomial.coe_C, HahnSeries.ofPowerSeries_C,
      LaurentSeries.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add, Polynomial.coe_add, hp, hq]
  | monomial n c _ih =>
    simp only [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X,
      HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X,
      LaurentSeries.algebraMap_apply, reciprocalGaugeW]

theorem reciprocalGaugeAction_padded (i m : ℕ) (him : i ≤ m) (y : LaurentSeries K) :
    reciprocalGaugeAction i y =
      ∑ k : Fin (m+1), Polynomial.aeval reciprocalGaugeZ
        (reciprocalGaugeCoefficient (K := K) i k.val) * reciprocalGaugeDz^[k.val] y := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => Polynomial.aeval reciprocalGaugeZ
      (reciprocalGaugeCoefficient (K := K) i k) * reciprocalGaugeDz^[k] y) (m+1)]
  unfold reciprocalGaugeAction
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right him 1))
  intro k hk hnot
  have hik : i < k := by
    have h := mt Finset.mem_range.mpr hnot
    omega
  rw [reciprocalGaugeCoefficient_above i k hik, map_zero, zero_mul]

/-- Clear the reciprocal denominator and preserve the exact Laurent input. -/
theorem reciprocalSourcePolynomial_kernel (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (G : LaurentSeries K)
    (hode : (∑ i, Polynomial.aeval reciprocalGaugeW (q i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) = 0) :
    (∑ k : Fin (m+1), Polynomial.aeval reciprocalGaugeZ
      (reciprocalSourcePolynomial m (reciprocalCommonDegree m q) q k.val) *
      reciprocalGaugeDz^[k.val] (reciprocalGaugeW * G)) = 0 := by
  let d := reciprocalCommonDegree m q
  let y := reciprocalGaugeW (K := K) * G
  have hit (i : Fin (m+1)) :
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G =
        ∑ k : Fin (m+1), Polynomial.aeval reciprocalGaugeZ
          (reciprocalGaugeCoefficient (K := K) i.val k.val) * reciprocalGaugeDz^[k.val] y := by
    calc
      _ = (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (reciprocalGaugeZ * y) := congrArg
            ((laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val])
              (reciprocalGauge_initial G).symm
      _ = reciprocalGaugeAction i.val y := reciprocalGauge_iterate i.val y
      _ = _ := reciprocalGaugeAction_padded i.val m (by omega) y
  have hr (i : Fin (m+1)) :=
    reciprocalGauge_reflect_eval d (q i) (reciprocalCommonDegree_bound m q i)
  have hc : (∑ i, Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d (q i)) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) = 0 := by
    calc
      _ = (reciprocalGaugeZ (K := K))^d *
          ∑ i, Polynomial.aeval reciprocalGaugeW (q i) *
            (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G := by
        simp only [hr,
          Finset.mul_sum, mul_assoc]
      _ = 0 := by rw [hode, mul_zero]
  rw [show (∑ k : Fin (m+1), Polynomial.aeval reciprocalGaugeZ
      (reciprocalSourcePolynomial m d q k.val) * reciprocalGaugeDz^[k.val] y) =
      ∑ i, Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d (q i)) *
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G from by
    simp only [reciprocalSourcePolynomial, map_sum, map_mul, Finset.sum_mul, hit,
      Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]]
  exact hc

theorem reciprocalGaugeZ_iterate (j : ℕ) (y : LaurentSeries K) :
    (fun x : LaurentSeries K => HahnSeries.single (-1 : ℤ) (1 : K) * x)^[j] y =
      (reciprocalGaugeZ (K := K))^j * y := by
  induction j with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ j ih => rw [Function.iterate_succ_apply', ih, pow_succ]; unfold reciprocalGaugeZ; ring

theorem reciprocalSourceArray_action (m d : ℕ) (q : Fin (m+1) → Polynomial K)
    (y : LaurentSeries K) :
    signedLaplaceSourceAction (reciprocalSourceArray m d q) y =
      ∑ k : Fin (m+1), Polynomial.aeval reciprocalGaugeZ
        (reciprocalSourcePolynomial m d q k.val) * reciprocalGaugeDz^[k.val] y := by
  unfold signedLaplaceSourceAction
  apply Finset.sum_congr rfl
  intro k hk
  rw [reciprocalSourceArray_polynomial m d q k]
  simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    Finset.sum_mul, LaurentSeries.algebraMap_apply, HahnSeries.C_apply,
    reciprocalGaugeZ_iterate, mul_assoc, reciprocalGaugeDz]
  rfl

/-- Any given nonzero ordinary polynomial ODE yields a nonzero finite source
array for the exact gauge w·G. No corner/Fuchs property is concluded. -/
theorem ordinaryODE_nonzero_reciprocal_source (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (hq : ∃ i, q i ≠ 0) (G : PowerSeries K)
    (hode : (∑ i, (q i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val] G) = 0) :
    let d := reciprocalCommonDegree m q
    let A := reciprocalSourceArray m d q
    (∃ i j, A i j ≠ 0) ∧
      signedLaplaceSourceAction A
        (HahnSeries.single (1 : ℤ) (1 : K) * HahnSeries.ofPowerSeries ℤ K G) = 0 := by
  dsimp only
  refine ⟨reciprocalSourceArray_nonzero m _ q hq, ?_⟩
  rw [reciprocalSourceArray_action]
  apply reciprocalSourcePolynomial_kernel
  have h := congrArg (HahnSeries.ofPowerSeries ℤ K) hode
  simpa only [map_sum, map_mul, map_zero, reciprocalGauge_aevalW,
    laurentOrdinaryDerivation_iterate_ofPowerSeries] using h

end StrictEUnit
end
