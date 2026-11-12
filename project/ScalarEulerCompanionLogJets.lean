import FrobeniusActualJetDeterminant

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The regular Euler companion of the literal scalar coefficient tuple.
Its final row divides by the SAME top power series, not a replacement operator. -/
def scalarEulerPowerSeriesCompanion (r : ℕ) (b : Fin (r+1) → PowerSeries K) :
    Matrix (Fin r) (Fin r) (PowerSeries K) := fun i j =>
  if i.val+1<r then (if j.val=i.val+1 then 1 else 0)
  else -((b (Fin.last r))⁻¹*b j.castSucc)

/-- The exact highest twisted Euler derivative follows from the literal
scalar equation and the nonzero constant coefficient of its top coefficient. -/
theorem scalarTwistedLogOperator_last_derivative (r : ℕ)
    (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (rho : K) (p : Polynomial (LaurentSeries K))
    (hp : scalarTwistedLogOperator r b rho p=0) :
    (twistedLogPolynomialEuler rho)^[r] p=
      ∑ j : Fin r,logPowerSeriesEmbedding (-((b (Fin.last r))⁻¹*b j.castSucc))*
        (twistedLogPolynomialEuler rho)^[j.val] p := by
  have he : (∑ j : Fin r,logPowerSeriesEmbedding (b j.castSucc)*
        (twistedLogPolynomialEuler rho)^[j.val] p)+
      logPowerSeriesEmbedding (b (Fin.last r))*(twistedLogPolynomialEuler rho)^[r] p=0 := by
    simpa only [scalarTwistedLogOperator,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last] using hp
  have hi : logPowerSeriesEmbedding ((b (Fin.last r))⁻¹)*
      logPowerSeriesEmbedding (b (Fin.last r))=1 := by
    rw [← map_mul,PowerSeries.inv_mul_cancel _ hb,map_one]
  have hlast : logPowerSeriesEmbedding (b (Fin.last r))*(twistedLogPolynomialEuler rho)^[r] p=
      -(∑ j : Fin r,logPowerSeriesEmbedding (b j.castSucc)*(twistedLogPolynomialEuler rho)^[j.val] p) := by
    exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using he)
  calc
    _=logPowerSeriesEmbedding ((b (Fin.last r))⁻¹)*
        (logPowerSeriesEmbedding (b (Fin.last r))*(twistedLogPolynomialEuler rho)^[r] p) := by rw [← mul_assoc,hi,one_mul]
    _=logPowerSeriesEmbedding ((b (Fin.last r))⁻¹)*
        (-(∑ j : Fin r,logPowerSeriesEmbedding (b j.castSucc)*(twistedLogPolynomialEuler rho)^[j.val] p)) := by rw [hlast]
    _=_ := by
      have hneg : ∀ x y : Polynomial (LaurentSeries K),x*(-y)= -(x*y) := by
        intro x y
        ring
      rw [hneg,Finset.mul_sum,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_neg,map_mul]
      ring


/-- The actual twisted jet of a scalar solution satisfies the SAME constructed
regular Euler companion equation. No vector equation is assumed. -/
theorem scalarTwistedEulerJet_solution (r : ℕ)
    (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (rho : K) (p : Polynomial (LaurentSeries K))
    (hp : scalarTwistedLogOperator r b rho p=0) (i : Fin r) :
    twistedLogPolynomialEuler rho ((twistedLogPolynomialEuler rho)^[i.val] p)=
      ∑ j,logPowerSeriesEmbedding (scalarEulerPowerSeriesCompanion r b i j)*
        (twistedLogPolynomialEuler rho)^[j.val] p := by
  by_cases hi : i.val+1<r
  · let k : Fin r := ⟨i.val+1,hi⟩
    have hj (j : Fin r) : j.val=i.val+1 ↔j=k :=
      ⟨fun h =>Fin.ext h,fun h =>congrArg Fin.val h⟩
    simp only [scalarEulerPowerSeriesCompanion,hi,if_true,hj,apply_ite,
      map_one,map_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    exact (Function.iterate_succ_apply' (twistedLogPolynomialEuler rho) i.val p).symm
  · have hn : i.val+1=r := by omega
    simp only [scalarEulerPowerSeriesCompanion,hi,if_false]
    rw [← Function.iterate_succ_apply' (twistedLogPolynomialEuler rho) i.val p,Nat.succ_eq_add_one,hn]
    exact scalarTwistedLogOperator_last_derivative r b hb rho p hp

/-- Constructed Frobenius columns satisfy the actual companion system; the
indicial kernel of every multiplicity seed was proved in the earlier construction. -/
theorem frobeniusActualJetMatrix_solution (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (hP : scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0)
    (e : frobeniusRootSeedIndex
      (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0) ≃ Fin r) :
    ∀ j i,twistedLogPolynomialEuler
      (frobeniusRootSeedExponent _ (e.symm j))
      (frobeniusActualJetMatrix (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) e i j)=
      ∑ l,logPowerSeriesEmbedding (scalarEulerPowerSeriesCompanion r b i l)*
        frobeniusActualJetMatrix (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))) e l j := by
  intro j i
  apply scalarTwistedEulerJet_solution r b hb _ _ ?_ i
  exact polynomialLogFrobeniusAmplitude_ring_equation r b _ _ hP
    (frobeniusRootSeedPolynomial_mem_kernel _ (e.symm j))

end StrictEUnit
end
