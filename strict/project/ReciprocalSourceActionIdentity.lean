import ReciprocalSourceEquation

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The full reciprocal/gauge identity, WITHOUT imposing the homogeneous
source equation. It retains the actual residual for every Laurent input. -/
theorem reciprocalSourceArray_action_identity (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G : LaurentSeries K) :
    signedLaplaceSourceAction (reciprocalSourceArray m (reciprocalCommonDegree m q) q)
      (reciprocalGaugeW*G)=
      (reciprocalGaugeZ (K:=K))^(reciprocalCommonDegree m q)*
        ∑ i,Polynomial.aeval reciprocalGaugeW (q i)*
          (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G := by
  let d := reciprocalCommonDegree m q
  let y := reciprocalGaugeW (K:=K)*G
  have hit (i : Fin (m+1)) :
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G=
        ∑ k : Fin (m+1),Polynomial.aeval reciprocalGaugeZ
          (reciprocalGaugeCoefficient (K:=K) i.val k.val)*reciprocalGaugeDz^[k.val] y := by
    calc
      _ = (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
          (reciprocalGaugeZ*y) := congrArg _ (reciprocalGauge_initial G).symm
      _ = reciprocalGaugeAction i.val y := reciprocalGauge_iterate i.val y
      _ = _ := reciprocalGaugeAction_padded i.val m (by omega) y
  rw [reciprocalSourceArray_action]
  change (∑ k : Fin (m+1),Polynomial.aeval reciprocalGaugeZ
    (reciprocalSourcePolynomial m d q k.val)*reciprocalGaugeDz^[k.val] y)=_
  calc
    _ = ∑ i : Fin (m+1),Polynomial.aeval reciprocalGaugeZ (Polynomial.reflect d (q i))*
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G := by
      simp only [reciprocalSourcePolynomial,map_sum,map_mul,Finset.sum_mul,hit,
        Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [reciprocalGauge_reflect_eval d _ (reciprocalCommonDegree_bound m q _),
        Finset.mul_sum,mul_assoc]
      rfl

/-- The original ordinary source residual, not the reciprocal array action. -/
def reciprocalOrdinarySourceAction (m : ℕ) (q : Fin (m+1) → Polynomial K)
    (G : PowerSeries K) : PowerSeries K :=
  ∑ i,(q i : PowerSeries K)*(PowerSeries.derivative K)^[i.val] G

theorem reciprocalSourceArray_powerSeries_action_identity (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G : PowerSeries K) :
    signedLaplaceSourceAction (reciprocalSourceArray m (reciprocalCommonDegree m q) q)
      (reciprocalGaugeW*HahnSeries.ofPowerSeries ℤ K G)=
      (reciprocalGaugeZ (K:=K))^(reciprocalCommonDegree m q)*
        HahnSeries.ofPowerSeries ℤ K (reciprocalOrdinarySourceAction m q G) := by
  rw [reciprocalSourceArray_action_identity]
  simp only [reciprocalOrdinarySourceAction,map_sum,map_mul,reciprocalGauge_aevalW,
    laurentOrdinaryDerivation_iterate_ofPowerSeries]

end StrictEUnit
end
