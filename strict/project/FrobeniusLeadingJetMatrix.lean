import FrobeniusHermiteJetSeparation

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The actual initial Wronskian jet: (D+rho)^i applied to X^j,
then evaluated at log zero. Every repeated root keeps its own log order. -/
def frobeniusLeadingJetMatrix {r : ℕ} (P : Polynomial K)
    (e : frobeniusRootSeedIndex P ≃ Fin r) : Matrix (Fin r) (Fin r) K := fun i j =>
  (((shiftedPolynomialDerivative (frobeniusRootSeedExponent P (e.symm j)))^[i.val])
    (frobeniusRootSeedPolynomial P (e.symm j))).coeff 0

/-- Row combinations are ordinary polynomial Hermite jets, with no
independence assumption on a solution family. -/
theorem frobeniusLeadingJetMatrix_vecMul {r : ℕ} (P : Polynomial K)
    (e : frobeniusRootSeedIndex P ≃ Fin r) (c : Fin r → K) (j : Fin r) :
    (Matrix.vecMul c (frobeniusLeadingJetMatrix P e)) j=
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[frobeniusRootSeedOrder P (e.symm j)]
        (frobeniusJetSymbol c)).eval (frobeniusRootSeedExponent P (e.symm j)) := by
  rw [← shiftedPolynomialDifferentialOperator_X_pow_coeff_zero]
  rw [frobeniusJetSymbol]
  simp only [shiftedPolynomialDifferentialOperator,map_sum,Polynomial.aeval_monomial,
    LinearMap.sum_apply,Module.End.mul_apply,Module.algebraMap_end_apply,
    Module.End.pow_apply,Polynomial.finset_sum_coeff,Polynomial.coeff_smul,smul_eq_mul]
  rfl

/-- Splitting and the exact multiplicity index prove invertibility of the
initial jet matrix, rather than postulating a nonzero Wronskian. -/
theorem frobeniusLeadingJetMatrix_isUnit {r : ℕ} (P : Polynomial K)
    (hP : P.Splits (RingHom.id K)) (e : frobeniusRootSeedIndex P ≃ Fin r) :
    IsUnit (frobeniusLeadingJetMatrix P e) := by
  apply Matrix.vecMul_injective_iff_isUnit.mp
  change Function.Injective (frobeniusLeadingJetMatrix P e).vecMulLinear
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro c hc
  have hcard : P.natDegree=r :=
    (frobeniusRootSeedIndex_card_natDegree P hP).symm.trans
      ((Fintype.card_congr e).trans (Fintype.card_fin r))
  have hQ : frobeniusJetSymbol c=0 := frobeniusRootSeed_hermite_separation P
    (frobeniusJetSymbol c) hP (by rw [hcard];exact frobeniusJetSymbol_degree_lt c) (by
      intro i
      have hh := congrFun hc (e i)
      change (Matrix.vecMul c (frobeniusLeadingJetMatrix P e)) (e i)=0 at hh
      rw [frobeniusLeadingJetMatrix_vecMul,Equiv.symm_apply_apply] at hh
      exact hh)
  apply frobeniusJetSymbol_injective
  simpa only [frobeniusJetSymbol,Pi.zero_apply,map_zero,Finset.sum_const_zero] using hQ

theorem frobeniusLeadingJetMatrix_det_ne_zero {r : ℕ} (P : Polynomial K)
    (hP : P.Splits (RingHom.id K)) (e : frobeniusRootSeedIndex P ≃ Fin r) :
    (frobeniusLeadingJetMatrix P e).det≠0 :=
  isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (frobeniusLeadingJetMatrix_isUnit P hP e))

end StrictEUnit
end
