import GeneralizedSourceReflection
import GeneralizedClearedCompanionJet

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Undo reflection of the full residual, rather than treating the reflected
and arithmetic source tuples as interchangeable. -/
theorem generalizedOrdinarySource_unreflection_iff (rho : K) (m : ℕ)
    (q : Fin (m+1) → Polynomial K) (G F : LaurentSeries (Polynomial K)) :
    (∑ i,logOrdinaryPolynomialImage (q i)*
      (generalizedLogOrdinaryDerivative rho)^[i.val] (logLaurentReflection G))=
        logLaurentReflection F ↔
    (∑ i,logOrdinaryPolynomialImage (ordinaryReflectionTuple m q i)*
      (generalizedLogOrdinaryDerivative rho)^[i.val] G)=F := by
  have he := generalizedOrdinarySource_reflection rho m q (logLaurentReflection G)
  rw [logLaurentReflection_involutive] at he
  rw [he]
  constructor
  · intro h
    rw [h,logLaurentReflection_involutive]
  · intro h
    have hh := congrArg logLaurentReflection h
    simpa only [logLaurentReflection_involutive] using hh

/-- The exact reflected scalar equation produces the canonical jet in the
original unreflected arithmetic companion. No analytic branch is asserted. -/
theorem generalizedSameCompanion_reflected_jet_iff
    (rho : K) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (G F : LaurentSeries (Polynomial K)) :
    (∀ i,generalizedLogOrdinaryDerivative rho
      (generalizedLogOrdinaryJet rho n (logLaurentReflection G) i)=
      (∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K)
        (minimalDerivativeCompanion (n+1) c i j))*generalizedLogOrdinaryJet rho n (logLaurentReflection G) j)+
        (if i.val=n then logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*logLaurentReflection F else 0)) ↔
    (∑ i : Fin ((n+1)+1),logOrdinaryPolynomialImage
      (ordinaryReflectionTuple (n+1) (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U) i)*
        (generalizedLogOrdinaryDerivative rho)^[i.val] G)=F := by
  rw [generalizedSameCompanion_jet_iff rho n c T U hT hclear]
  exact generalizedOrdinarySource_unreflection_iff rho (n+1) _ G F

end StrictEUnit
end
