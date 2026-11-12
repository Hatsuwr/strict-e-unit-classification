import ActualEulerFieldMap
import RetainedAmplitudeExactDescent

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

theorem logCoefficientFieldHom_double_coeff (phi : K →+* L)
    (u : LaurentSeries (Polynomial K)) (n : ℤ) (t : ℕ) :
    ((logCoefficientFieldHom phi u).coeff n).coeff t=phi ((u.coeff n).coeff t) := by
  change ((u.coeff n).map phi).coeff t=_
  exact Polynomial.coeff_map phi t

theorem logCoefficientFieldHom_injective (phi : K →+* L) :
    Function.Injective (logCoefficientFieldHom phi) := by
  intro u v he
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro t
  apply phi.injective
  simpa only [logCoefficientFieldHom_double_coeff] using
    congrArg (fun s : LaurentSeries (Polynomial L) =>(s.coeff n).coeff t) he

theorem logCoefficientFieldHom_smul (phi : K →+* L) (c : K)
    (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (c • u)=phi c • logCoefficientFieldHom phi u := by
  apply HahnSeries.ext
  funext n
  change (c • u.coeff n).map phi=phi c • (u.coeff n).map phi
  simp only [Polynomial.smul_eq_C_mul,Polynomial.map_mul,Polynomial.map_C]

theorem logCoefficientFieldHom_single_one (phi : K →+* L) (k : ℤ) :
    logCoefficientFieldHom phi (HahnSeries.single k (1:Polynomial K))=
      HahnSeries.single k (1:Polynomial L) := by
  apply HahnSeries.ext
  funext n
  change ((HahnSeries.single k (1:Polynomial K)).coeff n).map phi=_
  simp only [HahnSeries.coeff_single]
  split_ifs <;> simp

theorem logTargetX_field_map (phi : K →+* L) (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (logTargetX u)=logTargetX (logCoefficientFieldHom phi u) := by
  simp only [logTargetX,map_mul,logCoefficientFieldHom_single_one]

theorem logTargetNegativeDerivative_field_map (phi : K →+* L) (rho : K)
    (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (logTargetNegativeDerivative rho u)=
      logTargetNegativeDerivative (phi rho) (logCoefficientFieldHom phi u) := by
  simp only [logTargetNegativeDerivative,map_neg,map_mul,logCoefficientFieldHom_single_one,
    twistedLogCoefficientEuler_eq,actualEuler_field_map]

theorem generalizedLogFourierArrayAction_field_map {mu nu : ℕ} (phi : K →+* L)
    (rho : K) (A : Fin (mu+1) →Fin (nu+1) →K) (u : LaurentSeries (Polynomial K)) :
    logCoefficientFieldHom phi (generalizedLogFourierArrayAction rho A u)=
      generalizedLogFourierArrayAction (phi rho) (fun i j =>phi (A i j)) (logCoefficientFieldHom phi u) := by
  have hx (n : ℕ) (v : LaurentSeries (Polynomial K)) :
      logCoefficientFieldHom phi (logTargetX^[n] v)=logTargetX^[n] (logCoefficientFieldHom phi v) := by
    induction n with
    | zero =>rfl
    | succ n ih =>rw [Function.iterate_succ_apply',logTargetX_field_map,ih,Function.iterate_succ_apply']
  have hd (n : ℕ) (v : LaurentSeries (Polynomial K)) :
      logCoefficientFieldHom phi ((logTargetNegativeDerivative rho)^[n] v)=
        (logTargetNegativeDerivative (phi rho))^[n] (logCoefficientFieldHom phi v) := by
    induction n with
    | zero =>rfl
    | succ n ih =>rw [Function.iterate_succ_apply',logTargetNegativeDerivative_field_map,ih,Function.iterate_succ_apply']
  simp only [generalizedLogFourierArrayAction,map_sum,logCoefficientFieldHom_smul,hd,hx]

theorem logPolynomialToCoefficientSeries_field_map (phi : K →+* L)
    (f : Polynomial (LaurentSeries K)) :
    logCoefficientFieldHom phi (logPolynomialToCoefficientSeries f)=
      logPolynomialToCoefficientSeries (stage38_logMap phi f) := by
  apply HahnSeries.ext
  funext n
  apply Polynomial.ext
  intro t
  rw [logCoefficientFieldHom_double_coeff]
  rw [logPolynomialToCoefficientSeries_double_coeff,logPolynomialToCoefficientSeries_double_coeff,
    stage38_logMap_coeff]

/-- The exact Stage53 equation descends, not merely the amplitude's coefficients. -/
theorem actualTwistedStage53Action_field_iff {mu nu : ℕ} (phi : K →+* L)
    (rho : K) (A : Fin (mu+1) →Fin (nu+1) →K) (f : Polynomial (LaurentSeries K)) :
    actualTwistedStage53Action (phi rho) (fun i j =>phi (A i j)) (stage38_logMap phi f)=0 ↔
      actualTwistedStage53Action rho A f=0 := by
  rw [← fullArray_stage53_solution_iff,← fullArray_stage53_solution_iff,
    ← logPolynomialToCoefficientSeries_field_map,← generalizedLogFourierArrayAction_field_map]
  exact (logCoefficientFieldHom_injective phi).eq_iff' (map_zero _)

end StrictEUnit
end
