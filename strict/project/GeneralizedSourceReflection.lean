import GeneralizedLogReflection
import GeneralizedReciprocalSourceIdentity

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def logOrdinaryPolynomialImage : Polynomial K →+* LaurentSeries (Polynomial K) :=
  logLaurentCoefficientMap.comp (Polynomial.aeval (reciprocalGaugeW (K:=K))).toRingHom

theorem logOrdinaryPolynomialImage_C (c : K) :
    logOrdinaryPolynomialImage (Polynomial.C c)=HahnSeries.single 0 (Polynomial.C c) := by
  apply HahnSeries.ext
  funext n
  simp only [logOrdinaryPolynomialImage,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,Polynomial.aeval_C,logLaurentCoefficientMap_coeff,
    LaurentSeries.algebraMap_apply,HahnSeries.C_apply,HahnSeries.coeff_single]
  split_ifs <;> simp

theorem logOrdinaryPolynomialImage_X :
    logOrdinaryPolynomialImage (Polynomial.X:Polynomial K)=HahnSeries.single 1 (1:Polynomial K) := by
  apply HahnSeries.ext
  funext n
  simp only [logOrdinaryPolynomialImage,RingHom.comp_apply,AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,Polynomial.aeval_X,logLaurentCoefficientMap_coeff,
    reciprocalGaugeW,HahnSeries.coeff_single]
  split_ifs <;> simp

theorem logLaurentReflection_single (n : ℤ) (p : Polynomial K) :
    logLaurentReflection (HahnSeries.single n p)=HahnSeries.single n ((-1:K)^n • p) := by
  apply HahnSeries.ext
  funext k
  change (-1:K)^k • (HahnSeries.single n p).coeff k=_
  simp only [HahnSeries.coeff_single]
  split_ifs with h
  · subst k;rfl
  · simp

theorem logLaurentReflection_polynomial (p : Polynomial K) :
    logLaurentReflection (logOrdinaryPolynomialImage p)=
      logOrdinaryPolynomialImage (p.comp (-Polynomial.X)) := by
  have hh : (logLaurentReflectionHom (K:=K)).comp logOrdinaryPolynomialImage=
      logOrdinaryPolynomialImage.comp (Polynomial.compRingHom (-Polynomial.X)) := by
    apply Polynomial.ringHom_ext
    · intro c
      change logLaurentReflection (logOrdinaryPolynomialImage (Polynomial.C c))=
        logOrdinaryPolynomialImage ((Polynomial.C c).comp (-Polynomial.X))
      rw [Polynomial.C_comp,logOrdinaryPolynomialImage_C,logLaurentReflection_single]
      simp
    · change logLaurentReflection (logOrdinaryPolynomialImage (Polynomial.X:Polynomial K))=
        logOrdinaryPolynomialImage (Polynomial.X.comp (-Polynomial.X))
      rw [Polynomial.X_comp,map_neg,logOrdinaryPolynomialImage_X,logLaurentReflection_single]
      apply HahnSeries.ext
      funext n
      simp only [HahnSeries.coeff_neg,HahnSeries.coeff_single]
      split_ifs <;> simp
  exact RingHom.congr_fun hh p

/-- Exact reflection of the entire generalized source operator, including its
residual. It removes the qplus versus unreflected-q ambiguity. -/
theorem generalizedOrdinarySource_reflection (rho : K) (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G : LaurentSeries (Polynomial K)) :
    (∑ i,logOrdinaryPolynomialImage (ordinaryReflectionTuple m q i)*
      (generalizedLogOrdinaryDerivative rho)^[i.val] (logLaurentReflection G))=
      logLaurentReflection (∑ i,logOrdinaryPolynomialImage (q i)*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G) := by
  change _=logLaurentReflectionHom (∑ i,_)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change _=logLaurentReflection (_*_)
  rw [logLaurentReflection_mul,logLaurentReflection_polynomial,
    generalizedLogOrdinaryDerivative_reflection_iterate,ordinaryReflectionTuple,map_mul,
    logOrdinaryPolynomialImage_C,laurentCoefficient_smul_eq_mul]
  have hs : (-1:K)^i.val*(-1:K)^i.val=1 := by rw [← mul_pow];simp
  have hprod : HahnSeries.single 0 (Polynomial.C ((-1:K)^i.val))*
      HahnSeries.single 0 (Polynomial.C ((-1:K)^i.val))=(1:LaurentSeries (Polynomial K)) := by
    rw [HahnSeries.single_mul_single,← map_mul,hs,map_one]
    simp
  calc
    _=logOrdinaryPolynomialImage ((q i).comp (-Polynomial.X))*
      (HahnSeries.single 0 (Polynomial.C ((-1:K)^i.val))*HahnSeries.single 0 (Polynomial.C ((-1:K)^i.val)))*
      logLaurentReflection ((generalizedLogOrdinaryDerivative rho)^[i.val] G) := by ring
    _=_ := by rw [hprod,mul_one]

end StrictEUnit
end
