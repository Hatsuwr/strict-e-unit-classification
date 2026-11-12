import GeneralizedLogOrdinaryProduct
import OrdinaryBorelReflection

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Formal reflection t -> -t of the coefficient series. The external rho
and formal logarithm remain explicit; no analytic branch assertion is made. -/
def logLaurentReflection (s : LaurentSeries (Polynomial K)) : LaurentSeries (Polynomial K) where
  coeff n := (-1:K)^n • s.coeff n
  isPWO_support' := s.isPWO_support.mono (by
    intro n hn
    change s.coeff n≠0
    intro hz
    apply hn
    simp [hz])

theorem logLaurentReflection_support (s : LaurentSeries (Polynomial K)) :
    (logLaurentReflection s).support ⊆ s.support := by
  intro n hn
  change s.coeff n≠0
  intro hz
  apply hn
  change (-1:K)^n • s.coeff n=0
  rw [hz,smul_zero]

theorem logLaurentReflection_support_eq (s : LaurentSeries (Polynomial K)) :
    (logLaurentReflection s).support=s.support := by
  ext n
  change ((-1:K)^n • s.coeff n≠0) ↔ s.coeff n≠0
  simp [smul_eq_zero,zpow_ne_zero n (show (-1:K)≠0 from neg_ne_zero.mpr one_ne_zero)]

theorem logLaurentReflection_involutive (s : LaurentSeries (Polynomial K)) :
    logLaurentReflection (logLaurentReflection s)=s := by
  apply HahnSeries.ext
  funext n
  change (-1:K)^n • ((-1:K)^n • s.coeff n)=s.coeff n
  rw [smul_smul,← mul_zpow]
  simp

theorem logLaurentReflection_mul (f g : LaurentSeries (Polynomial K)) :
    logLaurentReflection (f*g)=logLaurentReflection f*logLaurentReflection g := by
  apply HahnSeries.ext
  funext n
  change (-1:K)^n • (f*g).coeff n=_
  rw [HahnSeries.coeff_mul,HahnSeries.coeff_mul]
  simp only [logLaurentReflection_support_eq]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1+ij.2=n := (Finset.mem_addAntidiagonal.mp hij).2.2
  change (-1:K)^n • (f.coeff ij.1*g.coeff ij.2)=
    ((-1:K)^ij.1 • f.coeff ij.1)*((-1:K)^ij.2 • g.coeff ij.2)
  rw [← hn,zpow_add₀ (neg_ne_zero.mpr one_ne_zero)]
  simp only [Polynomial.smul_eq_C_mul,map_mul]
  ring

def logLaurentReflectionHom : LaurentSeries (Polynomial K) →+* LaurentSeries (Polynomial K) where
  toFun := logLaurentReflection
  map_zero' := by apply HahnSeries.ext;funext n;exact smul_zero _
  map_one' := by
    apply HahnSeries.ext
    funext n
    change (-1:K)^n • (1:LaurentSeries (Polynomial K)).coeff n=_
    rw [HahnSeries.coeff_one]
    split_ifs with h
    · subst n;simp
    · simp
  map_add' f g := by
    apply HahnSeries.ext
    funext n
    change (-1:K)^n • (f+g).coeff n=_
    rw [HahnSeries.coeff_add,HahnSeries.coeff_add]
    exact smul_add _ _ _
  map_mul' := logLaurentReflection_mul

theorem logLaurentReflection_smul (a : K) (s : LaurentSeries (Polynomial K)) :
    logLaurentReflection (a • s)=a • logLaurentReflection s := by
  apply HahnSeries.ext
  funext n
  change (-1:K)^n • (a • s).coeff n=_
  simp only [HahnSeries.coeff_smul,logLaurentReflection,smul_smul,mul_comm]

/-- Exact anticommutation, with rho and logarithmic derivatives retained. -/
theorem generalizedLogOrdinaryDerivative_reflection (rho : K) (s : LaurentSeries (Polynomial K)) :
    generalizedLogOrdinaryDerivative rho (logLaurentReflection s)=
      -logLaurentReflection (generalizedLogOrdinaryDerivative rho s) := by
  apply HahnSeries.ext
  funext n
  simp only [generalizedLogOrdinaryDerivative,logMonomial_one_mul_coeff,HahnSeries.coeff_neg]
  change shiftedPolynomialDerivative (rho+(Int.cast (n-(-1:ℤ)) : K))
    ((-1:K)^(n-(-1:ℤ)) • s.coeff (n-(-1:ℤ))) =
      -((-1:K)^n • (HahnSeries.single (-1:ℤ) (1:Polynomial K)*twistedLogCoefficientEuler rho s).coeff n)
  rw [map_smul,logMonomial_one_mul_coeff]
  have hsign : (-1:K)^(n-(-1:ℤ)) = -((-1:K)^n) := by
    rw [sub_neg_eq_add,zpow_add₀ (neg_ne_zero.mpr one_ne_zero),zpow_one,mul_neg_one]
  rw [hsign,neg_smul]
  rfl

theorem generalizedLogOrdinaryDerivative_reflection_iterate (rho : K)
    (s : LaurentSeries (Polynomial K)) (i : ℕ) :
    (generalizedLogOrdinaryDerivative rho)^[i] (logLaurentReflection s)=
      (-1:K)^i • logLaurentReflection ((generalizedLogOrdinaryDerivative rho)^[i] s) := by
  have hsmul (a : K) (f : LaurentSeries (Polynomial K)) :
      generalizedLogOrdinaryDerivative rho (a • f)=a • generalizedLogOrdinaryDerivative rho f := by
    apply HahnSeries.ext
    funext n
    simp only [generalizedLogOrdinaryDerivative,logMonomial_one_mul_coeff,HahnSeries.coeff_smul]
    change shiftedPolynomialDerivative _ (a • f.coeff _) =a • shiftedPolynomialDerivative _ (f.coeff _)
    exact map_smul _ _ _
  induction i with
  | zero =>simp
  | succ i ih =>
    rw [Function.iterate_succ_apply',ih,hsmul,generalizedLogOrdinaryDerivative_reflection,
      Function.iterate_succ_apply',pow_succ,mul_neg_one]
    simp only [neg_smul,smul_neg]
    simp only [laurentCoefficient_smul_eq_mul,← HahnSeries.C_apply,map_neg]
    ring


end StrictEUnit
end
