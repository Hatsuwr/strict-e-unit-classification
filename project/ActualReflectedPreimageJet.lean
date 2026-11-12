import ReflectedGeneralizedCompanionJet

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual zero-class Fourier preimage has a canonical jet solving the
original arithmetic companion, with its exact reflected finite-Laurent forcing. -/
theorem actualStage53_zero_original_companion_jet
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (f : Polynomial (LaurentSeries K))
    (hf :
      let q := ordinaryReflectionTuple (n+1)
        (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)
      actualTwistedStage53Action 0 (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) f=0) :
    let q := ordinaryReflectionTuple (n+1)
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree+1) ∧
      ∃ P : Polynomial K,
      let G := logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)
      let F := logLaurentReflection (∑ j : Fin (P.natDegree+1),HahnSeries.single
        ((reciprocalCommonDegree (n+1) q:ℤ)-(j.val:ℤ)) (Polynomial.C (P.coeff j.val)))
      ∀ i,generalizedLogOrdinaryDerivative 0 (generalizedLogOrdinaryJet 0 n G i)=
        (∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K)
          (minimalDerivativeCompanion (n+1) c i j))*generalizedLogOrdinaryJet 0 n G j)+
          (if i.val=n then logLaurentCoefficientMap ((polynomialLaurentImage T)⁻¹)*F else 0) := by
  intro q
  obtain ⟨u,hu,hd,P,hP⟩ := actualStage53_zero_original_source_exists (n+1) q f hf
  refine ⟨u,hu,hd,P,?_⟩
  exact (generalizedSameCompanion_reflected_jet_iff 0 n c T U hT hclear
    (logLaurentCoefficientMap reciprocalGaugeZ*u) _).mpr hP

/-- Noninteger selected preimages similarly solve the unreflected arithmetic
companion, with no residual forcing. -/
theorem actualStage53_noninteger_original_companion_jet
    (rho : K) (hni : ∀ z : ℤ,rho≠(z:K))
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (f : Polynomial (LaurentSeries K))
    (hf :
      let q := ordinaryReflectionTuple (n+1)
        (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)
      actualTwistedStage53Action rho (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) f=0) :
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear rho (logMixing_noninteger_forward_nonzero rho hni) u=
        logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree) ∧
      let G := logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)
      ∀ i,generalizedLogOrdinaryDerivative rho (generalizedLogOrdinaryJet rho n G i)=
        ∑ j,logLaurentCoefficientMap (algebraMap (RatFunc K) (LaurentSeries K)
          (minimalDerivativeCompanion (n+1) c i j))*generalizedLogOrdinaryJet rho n G j := by
  let q := ordinaryReflectionTuple (n+1)
    (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)
  obtain ⟨u,hu,hd,hP⟩ := actualStage53_noninteger_original_source_exists rho hni (n+1) q f hf
  refine ⟨u,hu,hd,?_⟩
  have he := (generalizedSameCompanion_reflected_jet_iff rho n c T U hT hclear
    (logLaurentCoefficientMap reciprocalGaugeZ*u) 0).mpr hP
  have hz : logLaurentReflection (0:LaurentSeries (Polynomial K))=0 := logLaurentReflectionHom.map_zero
  simpa only [hz,mul_zero,ite_self,add_zero] using he


end StrictEUnit
end
