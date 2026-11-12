import GeneralizedMonomialEulerTransport
import OriginalSourceLaurentUnitPresentation
import ActualReflectedPreimageJet

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Generalized-log transport into the actual regular finite-Laurent extension.
This equivalence does not postulate a new regular matrix or its arithmetic. -/
theorem originalSource_generalized_finite_laurent_euler_iff
    (rho : K) (n : ℕ) (c : Fin (n+1) →RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1))
    (k : ℕ →ℤ) (s : ℕ) (v : Fin ((n+1)+s) →LaurentSeries (Polynomial K)) :
    let M := finiteLaurentOffset k s
    let A := finiteLaurentForcingConnection
      (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
      (clearedSourceForcingColumn n T) k s
    let w := finiteLaurentEulerWeights (fun i =>M+T.natTrailingDegree+i.val) (M+(n+1)) k s
    let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) (M+(n+1)) k s
    (∀ i,generalizedLogOrdinaryDerivative rho (v i)=∑ j,logLaurentCoefficientMap (A i j)*v j) ↔
      ∀ i,twistedLogCoefficientEuler rho (HahnSeries.single (w i:ℤ) (1:Polynomial K)*v i)=
        ∑ j,logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K (C i j))*
          (HahnSeries.single (w j:ℤ) (1:Polynomial K)*v j) := by
  exact generalizedMonomialEulerPresentation_solution_iff rho _ _ _
    (originalSource_finite_laurent_unit_euler_presentation n c T U hT hclear hV k s) v

/-- The noninteger actual reciprocal preimage now has a canonical solution of
the original regular Euler system, with all generalized log terms intact. -/
theorem actualStage53_noninteger_original_euler_solution
    (rho : K) (hni : ∀ z : ℤ,rho≠(z:K))
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K) (U i j)=
      algebraMap (Polynomial K) (RatFunc K) T*minimalDerivativeCompanion (n+1) c i j)
    (hV : ∀ j,U (Fin.last n) j≠0 →
      T.natTrailingDegree+j.val≤(U (Fin.last n) j).natTrailingDegree+(n+1))
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
      let x := fun i : Fin (n+1) =>HahnSeries.single ((T.natTrailingDegree+i.val:ℕ):ℤ)
        (1:Polynomial K)*generalizedLogOrdinaryJet rho n G i
      ∀ i,twistedLogCoefficientEuler rho (x i)=
        ∑ j,logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K
          (sourceLaurentEulerBase n T U 0 i j))*x j := by
  obtain ⟨u,hu,hd,hjet⟩ := actualStage53_noninteger_original_companion_jet rho hni n c T U hT hclear f hf
  refine ⟨u,hu,hd,?_⟩
  have he := (originalSource_generalized_finite_laurent_euler_iff rho n c T U hT hclear hV
    (fun _ =>0) 0 (generalizedLogOrdinaryJet rho n
      (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)))).mp hjet
  simpa only [finiteLaurentOffset,Finset.range_zero,Finset.sum_empty,zero_add,
    finiteLaurentEulerWeights,finiteLaurentEulerMatrix] using he

end StrictEUnit
end
