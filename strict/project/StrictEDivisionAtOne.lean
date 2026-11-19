import StrictEDivisionCoefficients
import StrictEDivisionODE
import Stage41GeometricEntireSeries

/-! NEW PROOF RECONSTRUCTION, not recovered historical source.
A rational strict-E factorial representation vanishing at one admits a genuine
strict-E quotient by z - 1, with no extra arithmetic, analytic, or ODE premise. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

/-- Cancel precisely the factorial factor introduced by shifting an EGF term. -/
theorem division_factorial_successor_term (b : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    ((n + 1 : ℂ) * b n) * z ^ (n + 1) / ((n + 1).factorial : ℂ) =
      z * (b n * z ^ n / (n.factorial : ℂ)) := by
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  <;> ring

/-- The coefficient recurrence gives the global product identity by shifting
an absolutely convergent factorial series. No power-series coercion is needed. -/
theorem division_egf_mul_sub_one_of_recurrence (a b : ℕ → ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => a n * z ^ n / (n.factorial : ℂ)) (f z))
    (D : ℝ) (hb : ∀ n, ‖b n‖ ≤ D ^ (n + 1))
    (hzero : b 0 = -a 0)
    (hnext : ∀ n, b (n + 1) = (n + 1 : ℂ) * b n - a (n + 1)) :
    ∀ z, (z - 1) * exponentialGeneratingFunction b z = f z := by
  intro z
  let u : ℕ → ℂ := fun n => (a n + b n) * z ^ n / (n.factorial : ℂ)
  have hu0 : u 0 = 0 := by
    dsimp [u]
    simp only [hzero, add_neg_cancel, zero_mul, zero_div]
  have hu : HasSum u (f z + exponentialGeneratingFunction b z) := by
    convert (hs z).add (geometric_egf_hasSum b D hb z) using 1
    funext n
    dsimp [u]
    ring
  have ht : HasSum (fun n => u (n + 1))
      (z * exponentialGeneratingFunction b z) := by
    convert (geometric_egf_hasSum b D hb z).mul_left z using 1
    funext n
    change (a (n + 1) + b (n + 1)) * z ^ (n + 1) /
      ((n + 1).factorial : ℂ) = _
    have hab : a (n + 1) + b (n + 1) = (n + 1 : ℂ) * b n := by
      rw [hnext]
      ring
    rw [hab]
    exact division_factorial_successor_term b z n
  have hfull : HasSum u (z * exponentialGeneratingFunction b z) := by
    have h := (hasSum_nat_add_iff (f := u) 1).mp ht
    simpa only [Finset.sum_range_one, hu0, add_zero] using h
  have heq := hu.unique hfull
  calc
    (z - 1) * exponentialGeneratingFunction b z =
        z * exponentialGeneratingFunction b z - exponentialGeneratingFunction b z := by ring
    _ = (f z + exponentialGeneratingFunction b z) - exponentialGeneratingFunction b z := by
      rw [← heq]
    _ = f z := add_sub_cancel_right _ _

/-- A zero at one and rational factorial coefficients give a full strict-E
quotient. The original common denominators suffice, the tail identity supplies
all conjugate bounds, and the ODE is reconstructed in the actual Laurent field. -/
theorem strictEFunction_divAtOne_of_rational_representation
    {f : ℂ → ℂ} (hf : IsStrictEFunction f) (a : ℕ → AlgebraicComplex)
    (hrat : ∀ n, ∃ q : ℚ, a n = algebraMap ℚ AlgebraicComplex q)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (hz : f 1 = 0) :
    ∃ g : ℂ → ℂ, IsStrictEFunction g ∧ ∀ z, (z - 1) * g z = f z := by
  have hd := strictEFunction_differentiable hf
  have ha := strictEArithmetic_of_factorial_representation hf a hs
  have hzero : HasSum (fun n => (a n : ℂ) / (n.factorial : ℂ)) 0 := by
    simpa only [one_pow, mul_one, hz] using hs 1
  let b : ℕ → AlgebraicComplex := strictEDivisionCoeff a
  have hab : HasStrictEArithmetic b := strictEArithmetic_divisionCoeff a ha hrat hzero
  obtain ⟨D, hD, hb⟩ := strictEArithmetic_chosen_bound hab
  let g : ℂ → ℂ := exponentialGeneratingFunction (fun n => (b n : ℂ))
  have hdg : Differentiable ℂ g :=
    stage41_geometric_egf_differentiable (fun n => (b n : ℂ)) D hb
  have hsg : ∀ z, HasSum (fun n => (b n : ℂ) * z ^ n / (n.factorial : ℂ)) (g z) :=
    geometric_egf_hasSum (fun n => (b n : ℂ)) D hb
  have hmul : ∀ z, (z - 1) * g z = f z := by
    apply division_egf_mul_sub_one_of_recurrence (fun n => (a n : ℂ))
      (fun n => (b n : ℂ)) f hd hs D hb
    · simp [b, strictEDivisionCoeff]
    · intro n
      simp [b, strictEDivisionCoeff]
  have hcoeff (n : ℕ) : entireCauchyCoefficient g n =
      (b n : ℂ) / (n.factorial : ℂ) :=
    stage41_geometric_egf_cauchyCoefficient (fun j => (b j : ℂ)) D hb n
  let G : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield :=
    ⟨⟨g, hdg⟩, (mem_subfieldEntireFunctionAlgebra _ _).mpr (by
      intro n
      rw [hcoeff]
      exact (algebraicClosure ℚ ℂ).toSubfield.div_mem (b n).property (natCast_mem _ _))⟩
  have hode : HasAlgebraicPolynomialODE g := by
    apply (stage14_algebraicPolynomialODE_iff_subfield g).mpr
    exact division_actualSubfieldODE_of_polynomial_mul
      (algebraicClosure ℚ ℂ).toSubfield (strictEFunctionTaylorRealization f hf) G
      (Polynomial.X - Polynomial.C 1) (Polynomial.X_sub_C_ne_zero 1)
      ((stage14_algebraicPolynomialODE_iff_subfield f).mp hf.choose_spec.2.2.1)
      (by
        intro z
        change (Polynomial.X - Polynomial.C (1 : AlgebraicComplex)).eval₂
          (algebraicClosure ℚ ℂ).val.toRingHom z * g z = f z
        simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C,
          Polynomial.eval₂_one, map_one] using hmul z)
  exact ⟨g, ⟨b, hdg, hsg, hode, hab⟩, hmul⟩

end StrictEUnit

#print axioms StrictEUnit.strictEFunction_divAtOne_of_rational_representation
