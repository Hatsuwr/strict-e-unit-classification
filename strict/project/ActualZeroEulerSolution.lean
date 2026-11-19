import ReflectedResidualConstantAssembly

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Actual zero-class reciprocal preimage, including its reflected Laurent residual,
now yields a solution of the same regular Euler extension used by arithmetic. -/
theorem actualStage53_zero_original_euler_solution
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
      actualTwistedStage53Action 0 (reciprocalSourceArray (n+1) (reciprocalCommonDegree (n+1) q) q) f=0) :
    let q := ordinaryReflectionTuple (n+1)
      (sameCompanionScalarTuple (n+1) (Nat.succ_pos n) T U)
    ∃ u : LaurentSeries (Polynomial K),
      generalizedLogLaplaceLinear 0 logMixing_zero_forward_nonzero u=logPolynomialToCoefficientSeries f ∧
      (∀ m,(u.coeff m).natDegree≤f.natDegree+1) ∧
      ∃ P : Polynomial K,
      let G := logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u)
      let d := reciprocalCommonDegree (n+1) q
      let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
      let M := finiteLaurentOffset k (P.natDegree+1)
      let v := parallelForcingVector (generalizedLogOrdinaryJet 0 n G)
        (reflectedResidualConstant d P) (P.natDegree+1)
      let w := finiteLaurentEulerWeights (fun i =>M+T.natTrailingDegree+i.val)
        (M+(n+1)) k (P.natDegree+1)
      let x := fun i =>HahnSeries.single (w i:ℤ) (1:Polynomial K)*v i
      ∀ i,twistedLogCoefficientEuler 0 (x i)=
        ∑ j,logLaurentCoefficientMap (HahnSeries.ofPowerSeries ℤ K
          (finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
            (augmentedSourceEulerColumn n T) (M+(n+1)) k (P.natDegree+1) i j))*x j := by
  intro q
  obtain ⟨u,hu,hd,P,hjet⟩ := actualStage53_zero_original_companion_jet n c T U hT hclear f hf
  refine ⟨u,hu,hd,P,?_⟩
  have hext := reflectedResidual_constant_extension n (reciprocalCommonDegree (n+1) q) T P
    (Matrix.map (minimalDerivativeCompanion (n+1) c) (algebraMap (RatFunc K) (LaurentSeries K)))
    (generalizedLogOrdinaryJet 0 n (logLaurentReflection (logLaurentCoefficientMap reciprocalGaugeZ*u))) hjet
  exact (originalSource_generalized_finite_laurent_euler_iff 0 n c T U hT hclear hV
    (fun j =>(reciprocalCommonDegree (n+1) q:ℤ)-(j:ℤ)) (P.natDegree+1) _).mp hext

end StrictEUnit
end
