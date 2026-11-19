import GeneralizedReciprocalGauge
import ReciprocalSourceActionIdentity
import GeneralizedLogFourierArrayTransport

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem generalizedReciprocalGaugeAction_padded (rho : K) (i m : ℕ) (him : i≤m)
    (y : LaurentSeries (Polynomial K)) :
    generalizedReciprocalGaugeAction rho i y=
      ∑ k : Fin (m+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
        (reciprocalGaugeCoefficient (K:=K) i k.val))*(reciprocalLogSeriesDerivative rho)^[k.val] y := by
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
      (reciprocalGaugeCoefficient (K:=K) i k))*(reciprocalLogSeriesDerivative rho)^[k] y) (m+1)]
  unfold generalizedReciprocalGaugeAction
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right him 1))
  intro k hk hnot
  have hik : i<k := by
    have h := mt Finset.mem_range.mpr hnot
    omega
  rw [reciprocalGaugeCoefficient_above i k hik,map_zero,map_zero,zero_mul]

theorem logSourceZ_iterate (j : ℕ) (y : LaurentSeries (Polynomial K)) :
    logSourceZ^[j] y=(logLaurentCoefficientMap (reciprocalGaugeZ (K:=K)))^j*y := by
  induction j with
  | zero =>simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,pow_succ]
    rw [logLaurentCoefficientMap_reciprocalZ]
    unfold logSourceZ
    ring

theorem generalizedReciprocalSourceArray_action (rho : K) (m d : ℕ)
    (q : Fin (m+1) → Polynomial K) (y : LaurentSeries (Polynomial K)) :
    generalizedLogSourceArrayAction rho (reciprocalSourceArray m d q) y=
      ∑ k : Fin (m+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
        (reciprocalSourcePolynomial m d q k.val))*(reciprocalLogSeriesDerivative rho)^[k.val] y := by
  unfold generalizedLogSourceArrayAction
  apply Finset.sum_congr rfl
  intro k hk
  rw [reciprocalSourceArray_polynomial m d q k]
  simp only [map_sum,map_mul,map_pow,Polynomial.aeval_C,Polynomial.aeval_X,Finset.sum_mul,
    logSourceZ_iterate,laurentCoefficient_smul_eq_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  apply HahnSeries.ext
  funext n
  simp only [logLaurentCoefficientMap_coeff,LaurentSeries.algebraMap_apply,HahnSeries.C_apply,
    HahnSeries.coeff_single]
  split_ifs <;> simp

/-- Full actual source-array identity for arbitrary external rho and finite-log
Laurent input. No homogeneous source equation is assumed. -/
theorem generalizedReciprocalSourceArray_action_identity (rho : K) (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G : LaurentSeries (Polynomial K)) :
    generalizedLogSourceArrayAction rho
      (reciprocalSourceArray m (reciprocalCommonDegree m q) q)
        (logLaurentCoefficientMap reciprocalGaugeW*G)=
      (logLaurentCoefficientMap (reciprocalGaugeZ (K:=K)))^(reciprocalCommonDegree m q)*
        ∑ i,logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeW (q i))*
          (generalizedLogOrdinaryDerivative rho)^[i.val] G := by
  let d := reciprocalCommonDegree m q
  let y := logLaurentCoefficientMap (reciprocalGaugeW (K:=K))*G
  have hinitial : logLaurentCoefficientMap reciprocalGaugeZ*y=G := by
    rw [show logLaurentCoefficientMap reciprocalGaugeZ*y=
      logLaurentCoefficientMap (reciprocalGaugeZ*reciprocalGaugeW)*G by simp only [map_mul,y,mul_assoc],
      reciprocalGauge_inverse,map_one,one_mul]
  have hit (i : Fin (m+1)) :
      (generalizedLogOrdinaryDerivative rho)^[i.val] G=
        ∑ k : Fin (m+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
          (reciprocalGaugeCoefficient (K:=K) i.val k.val))*(reciprocalLogSeriesDerivative rho)^[k.val] y := by
    calc
      _=(generalizedLogOrdinaryDerivative rho)^[i.val]
          (logLaurentCoefficientMap reciprocalGaugeZ*y) := congrArg _ hinitial.symm
      _=generalizedReciprocalGaugeAction rho i.val y := generalizedReciprocalGauge_iterate rho i.val y
      _=_ := generalizedReciprocalGaugeAction_padded rho i.val m (by omega) y
  rw [generalizedReciprocalSourceArray_action]
  change (∑ k : Fin (m+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ
    (reciprocalSourcePolynomial m d q k.val))*(reciprocalLogSeriesDerivative rho)^[k.val] y)=_
  calc
    _=∑ i : Fin (m+1),logLaurentCoefficientMap (Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d (q i)))*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G := by
      simp only [reciprocalSourcePolynomial,map_sum,map_mul,Finset.sum_mul,hit,Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _=_ := by
      simp only [reciprocalGauge_reflect_eval d _ (reciprocalCommonDegree_bound m q _),
        map_mul,map_pow,Finset.mul_sum,mul_assoc]
      rfl

end StrictEUnit
end
