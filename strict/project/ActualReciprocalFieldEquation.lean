import ActualFourierFieldDescent
import ReciprocalArrayFieldMap

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

/-- Reconcile the dependent Fourier order by rewriting the literal finite sum,
not by assuming the two array types are definitionally equal. -/
theorem generalizedLogFourier_reciprocal_field_map
    (phi : K →+* L) (rho : K) (m d : ℕ) (q : Fin (m+1) →Polynomial K)
    (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (generalizedLogFourierArrayAction rho (reciprocalSourceArray m d q) u)=
      generalizedLogFourierArrayAction (phi rho)
        (reciprocalSourceArray m d (fun i =>(q i).map phi)) (logCoefficientFieldHom phi u) := by
  rw [generalizedLogFourierArrayAction_field_map]
  unfold generalizedLogFourierArrayAction
  apply Finset.sum_congr rfl
  intro i hi
  simp only [reciprocalSourceArray,← reciprocalSourcePolynomial_field_map,Polynomial.coeff_map]
  rw [Fin.sum_univ_eq_sum_range (fun j =>phi ((reciprocalSourcePolynomial m d q i.val).coeff j) •
      (logTargetNegativeDerivative (phi rho))^[j] (logTargetX^[i.val] (logCoefficientFieldHom phi u))),
    Fin.sum_univ_eq_sum_range (fun j =>phi ((reciprocalSourcePolynomial m d q i.val).coeff j) •
      (logTargetNegativeDerivative (phi rho))^[j] (logTargetX^[i.val] (logCoefficientFieldHom phi u)))]
  rw [reciprocalSourceDegree_field_map]

/-- The actual reciprocal Stage53 equation is preserved and reflected under
field extension even though its finite index type contains computed degrees. -/
theorem actualStage53_reciprocal_field_iff
    (phi : K →+* L) (rho : K) (m d : ℕ) (q : Fin (m+1) →Polynomial K)
    (f : Polynomial (LaurentSeries K)) :
    actualTwistedStage53Action (phi rho) (reciprocalSourceArray m d (fun i =>(q i).map phi))
      (stage38_logMap phi f)=0 ↔
    actualTwistedStage53Action rho (reciprocalSourceArray m d q) f=0 := by
  rw [← fullArray_stage53_solution_iff,← fullArray_stage53_solution_iff,
    ← logPolynomialToCoefficientSeries_field_map,← generalizedLogFourier_reciprocal_field_map]
  exact (logCoefficientFieldHom_injective phi).eq_iff' (map_zero _)

/-- Descent for the exact image tuple and exact mapped-back amplitude. -/
theorem actualStage53_reciprocal_image_descent
    (phi : K →+* L) (rho : K) (m : ℕ)
    (q : Fin (m+1) →Polynomial K) (qL : Fin (m+1) →Polynomial L)
    (hq : qL=fun i =>(q i).map phi)
    (f : Polynomial (LaurentSeries K)) (fL : Polynomial (LaurentSeries L))
    (hf : stage38_logMap phi f=fL)
    (hsol : actualTwistedStage53Action (phi rho)
      (reciprocalSourceArray m (reciprocalCommonDegree m qL) qL) fL=0) :
    actualTwistedStage53Action rho (reciprocalSourceArray m (reciprocalCommonDegree m q) q) f=0 := by
  subst qL
  rw [reciprocalCommonDegree_field_map,← hf] at hsol
  exact (actualStage53_reciprocal_field_iff phi rho m (reciprocalCommonDegree m q) q f).mp hsol

end StrictEUnit
end
