import FrobeniusOperatorBaseChange
import Stage26FiniteCoefficientField

/-! The SAME explicit recurrence commutes with field embeddings, including
its resonant branches. Its infinitely many coefficients therefore remain in
any fixed field containing the operator, exponent and seed coefficients. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] (φ : K →+* L)

theorem shiftedPolynomialDifferentialOperator_map (c : K) (P p : Polynomial K) :
    (shiftedPolynomialDifferentialOperator c P p).map φ =
      shiftedPolynomialDifferentialOperator (φ c) (P.map φ) (p.map φ) := by
  simp only [shiftedPolynomialDifferentialOperator_eq,polynomialDifferentialOperator_map,
    Polynomial.map_comp,Polynomial.map_add,Polynomial.map_X,Polynomial.map_C]

theorem polynomialLogLowerSum_map (B : ℕ → Polynomial K) (rho : K) (n : ℕ)
    (v : Fin n → Polynomial K) :
    (polynomialLogLowerSum B rho n v).map φ =
      polynomialLogLowerSum (fun k => (B k).map φ) (φ rho) n (fun i => (v i).map φ) := by
  simp only [polynomialLogLowerSum,Polynomial.map_sum,shiftedPolynomialDifferentialOperator_map,
    map_add,map_natCast]

variable [CharZero K] [CharZero L]

theorem polynomialLogFrobeniusCoefficient_map (B : ℕ → Polynomial K) (rho : K)
    (u0 : Polynomial K) (n : ℕ) :
    (polynomialLogFrobeniusCoefficient B rho u0 n).map φ =
      polynomialLogFrobeniusCoefficient (fun k => (B k).map φ) (φ rho) (u0.map φ) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [polynomialLogFrobeniusCoefficient_eq,polynomialLogFrobeniusCoefficient_eq]
    by_cases hn : n = 0
    · simp only [if_pos hn]
    · simp only [if_neg hn,shiftedPolynomialDifferentialRightInverse_map,
        Polynomial.map_neg,polynomialLogLowerSum_map,map_add,map_natCast]
      congr 3
      funext i
      exact ih i.1 i.2

section IntermediateField
variable [Algebra ℚ K]

/-- A concrete polynomial lift, not a selection of a replacement solution. -/
def polynomialRestrictToField (F : IntermediateField ℚ K) (p : Polynomial K)
    (hp : ∀ j,p.coeff j ∈ F) : Polynomial F :=
  ∑ j ∈ p.support,Polynomial.monomial j ⟨p.coeff j,hp j⟩

theorem polynomialRestrictToField_map (F : IntermediateField ℚ K) (p : Polynomial K)
    (hp : ∀ j,p.coeff j ∈ F) :
    (polynomialRestrictToField F p hp).map (algebraMap F K) = p := by
  simp only [polynomialRestrictToField,Polynomial.map_sum,Polynomial.map_monomial]
  simpa only [Polynomial.sum_def] using Polynomial.sum_monomial_eq p

/-- A single field contains EVERY coefficient at EVERY recurrence index. -/
theorem polynomialLogFrobeniusCoefficient_mem_field
    (F : IntermediateField ℚ K) (B : ℕ → Polynomial K) (rho : K) (u0 : Polynomial K)
    (hB : ∀ n j,(B n).coeff j ∈ F) (hrho : rho ∈ F) (hu0 : ∀ j,u0.coeff j ∈ F)
    (n j : ℕ) : (polynomialLogFrobeniusCoefficient B rho u0 n).coeff j ∈ F := by
  let BF : ℕ → Polynomial F := fun n => polynomialRestrictToField F (B n) (hB n)
  let uF := polynomialRestrictToField F u0 hu0
  let rhoF : F := ⟨rho,hrho⟩
  have hmap := polynomialLogFrobeniusCoefficient_map (algebraMap F K) BF rhoF uF n
  have hBF : (fun k => (BF k).map (algebraMap F K)) = B := by
    funext k
    exact polynomialRestrictToField_map F (B k) (hB k)
  rw [hBF,show uF.map (algebraMap F K) = u0 from polynomialRestrictToField_map F u0 hu0] at hmap
  change (polynomialLogFrobeniusCoefficient BF rhoF uF n).map (algebraMap F K) =
    polynomialLogFrobeniusCoefficient B rho u0 n at hmap
  rw [← hmap,Polynomial.coeff_map]
  exact (polynomialLogFrobeniusCoefficient BF rhoF uF n).coeff j |>.property

/-- Full Laurent/log coefficient descent for the exact constructed amplitude,
including all negative coefficients. -/
theorem polynomialLogFrobeniusAmplitude_mem_field
    (F : IntermediateField ℚ K) (B : ℕ → Polynomial K) (rho : K) (u0 : Polynomial K)
    (hB : ∀ n j,(B n).coeff j ∈ F) (hrho : rho ∈ F) (hu0 : ∀ j,u0.coeff j ∈ F)
    (j : ℕ) (n : ℤ) : ((polynomialLogFrobeniusAmplitude B rho u0).coeff j).coeff n ∈ F := by
  cases n with
  | ofNat n =>
    simp only [Int.ofNat_eq_coe]
    rw [polynomialLogFrobeniusAmplitude_coeff]
    exact polynomialLogFrobeniusCoefficient_mem_field F B rho u0 hB hrho hu0 n j
  | negSucc n =>
    rw [polynomialLogFrobeniusAmplitude_negative_coeff _ _ _ _ (Int.negSucc_lt_zero n)]
    exact F.zero_mem

end IntermediateField
end StrictEUnit
end

#print axioms StrictEUnit.shiftedPolynomialDifferentialOperator_map
#print axioms StrictEUnit.polynomialLogLowerSum_map
#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient_map
#print axioms StrictEUnit.polynomialRestrictToField_map
#print axioms StrictEUnit.polynomialLogFrobeniusCoefficient_mem_field
#print axioms StrictEUnit.polynomialLogFrobeniusAmplitude_mem_field
