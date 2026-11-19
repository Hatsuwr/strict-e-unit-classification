import TwistedScalarJetElimination

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem rationalTwistedTopDerivative (rho : K)
    (p : Polynomial (LaurentSeries K)) (n : ℕ)
    (q : Fin (n+1+1) → RatFunc K) (hq : q (Fin.last (n+1))≠0)
    (h : (∑ j,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q j))*
      (actualTwistedLogOrdinary rho)^[j.val] p)=0) :
    (actualTwistedLogOrdinary rho)^[n+1] p=
      ∑ j : Fin (n+1),Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K)
        (-(q (Fin.last (n+1)))⁻¹*q j.castSucc))*
        (actualTwistedLogOrdinary rho)^[j.val] p := by
  rw [Fin.sum_univ_castSucc] at h
  have ht : Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q (Fin.last (n+1))))*
      (actualTwistedLogOrdinary rho)^[n+1] p =
      -(∑ j : Fin (n+1),Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q j.castSucc))*
        (actualTwistedLogOrdinary rho)^[j.val] p) := by
    exact eq_neg_of_add_eq_zero_right h
  have he := congrArg (fun z : Polynomial (LaurentSeries K) =>
      Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) ((q (Fin.last (n+1)))⁻¹))*z) ht
  simp only [← mul_assoc,← map_mul,inv_mul_cancel₀ hq,map_one,one_mul] at he
  rw [he]
  simp only [map_mul,map_neg,Finset.mul_sum,mul_neg,neg_mul,mul_assoc,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem rationalTwistedEquation_coefficient_polynomialODE (rho : K)
    (p : Polynomial (LaurentSeries K)) (n : ℕ)
    (q : Fin (n+1+1) → RatFunc K) (hq : q (Fin.last (n+1))≠0)
    (h : (∑ j,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (q j))*
      (actualTwistedLogOrdinary rho)^[j.val] p)=0) :
    ∀ j,HasPolynomialScalarDifferentialRelation (k:=K)
      stage14_laurentAlgebraDerivation (p.coeff j) :=
  twistedScalarJet_coefficient_polynomialODE rho p n _
    (rationalTwistedTopDerivative rho p n q hq h)
end StrictEUnit
end
