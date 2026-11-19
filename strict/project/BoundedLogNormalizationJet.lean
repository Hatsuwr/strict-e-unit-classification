import FrobeniusIndicialDenominatorPower
import FallingCompositeFilterIdentities

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K]

/-- Only this finite jet acts on logarithmic polynomials of degree at most d. -/
def polynomialLowJet (P : Polynomial K) (d : ℕ) : Polynomial K :=
  ∑ k ∈ Finset.range (d+1),Polynomial.monomial k (P.coeff k)

theorem polynomialLowJet_coeff (P : Polynomial K) (d j : ℕ) :
    (polynomialLowJet P d).coeff j=if j≤d then P.coeff j else 0 := by
  classical
  simp only [polynomialLowJet,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range,Nat.lt_succ_iff]

theorem polynomialDifferentialOperator_eq_of_low_coeff (P Q f : Polynomial K)
    (d : ℕ) (hf : f.natDegree≤d) (hPQ : ∀ j,j≤d → P.coeff j=Q.coeff j) :
    polynomialDifferentialOperator P f=polynomialDifferentialOperator Q f := by
  have hz : polynomialDifferentialOperator (P-Q) f=0 := by
    rw [polynomialDifferentialOperator_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hid : i≤d
    · rw [Polynomial.coeff_sub,hPQ i hid,sub_self,zero_smul]
    · rw [Polynomial.iterate_derivative_eq_zero (lt_of_le_of_lt hf (Nat.lt_of_not_ge hid)),smul_zero]
  simpa only [polynomialDifferentialOperator,map_sub,LinearMap.sub_apply,sub_eq_zero] using hz

theorem polynomialLowJet_differential (P f : Polynomial K) (d : ℕ)
    (hf : f.natDegree≤d) :
    polynomialDifferentialOperator (polynomialLowJet P d) f=polynomialDifferentialOperator P f := by
  apply polynomialDifferentialOperator_eq_of_low_coeff _ _ f d hf
  intro j hj
  rw [polynomialLowJet_coeff,if_pos hj]

/-- Precise finite-jet normalization certificate. Its coefficient-clearing and
nonzero-pivot premises remain explicit; no exponential bound for either is
asserted here. In particular, bijectivity alone is not used as arithmetic. -/
theorem shiftedPolynomialDifferentialEquation_lowJet_pivot_clearing
    (P f : Polynomial K) (alpha D : K) (e d : ℕ) (he : 0<e)
    (hpivot : P.eval alpha≠0) (hf : f.natDegree≤d)
    (hjet : ∀ j,j≤d → IsIntegral ℤ ((e : K)*
      (P.comp (Polynomial.X+Polynomial.C alpha)).coeff j))
    (hforced : ∀ j,IsIntegral ℤ (D*(shiftedPolynomialDifferentialOperator alpha P f).coeff j))
    [CharZero K] :
    ∀ j,IsIntegral ℤ (((e : K)*P.eval alpha)^(d+1)*D*f.coeff j) := by
  let Q := P.comp (Polynomial.X+Polynomial.C alpha)
  let J := Polynomial.C (e : K)*polynomialLowJet Q d
  have hJ (j : ℕ) : IsIntegral ℤ (J.coeff j) := by
    dsimp only [J]
    rw [Polynomial.coeff_C_mul,polynomialLowJet_coeff]
    split_ifs with hj
    · exact hjet j hj
    · simpa only [mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : K))
  have hJ0 : J.coeff 0=(e : K)*P.eval alpha := by
    dsimp only [J]
    rw [Polynomial.coeff_C_mul,polynomialLowJet_coeff,if_pos (Nat.zero_le d)]
    dsimp only [Q]
    rw [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C,zero_add]
  have hJne : J.coeff 0≠0 := by
    rw [hJ0]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt he)) hpivot
  have hact : polynomialDifferentialOperator J (D • f)=
      (e : K) • (D • shiftedPolynomialDifferentialOperator alpha P f) := by
    rw [map_smul]
    dsimp only [J]
    rw [polynomialDifferentialOperator_mul]
    simp only [polynomialDifferentialOperator,Polynomial.aeval_C,Module.algebraMap_end_apply]
    change D • ((e : K) • polynomialDifferentialOperator (polynomialLowJet Q d) f)=_
    rw [polynomialLowJet_differential Q f d hf,← shiftedPolynomialDifferentialOperator_eq]
    exact smul_comm D (e : K) _
  have hforce (j : ℕ) : IsIntegral ℤ ((polynomialDifferentialOperator J (D • f)).coeff j) := by
    rw [hact]
    simp only [Polynomial.coeff_smul,smul_eq_mul]
    exact (ordinaryJet_natCast_integral e).mul (hforced j)
  have h := polynomialDifferentialEquation_integral_pivot_power J (D • f) hJ hJne d
    ((Polynomial.natDegree_smul_le _ _).trans hf) hforce
  simpa only [hJ0,Polynomial.coeff_smul,smul_eq_mul,mul_assoc] using h

end StrictEUnit
end
