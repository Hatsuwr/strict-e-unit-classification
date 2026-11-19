import V5BroadAlgebraicDescent

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Actual broad E-functions: use the same entire-function, complex series and
algebraic ODE conventions as in the strict predicate, with broad growth. -/
def V5IsBroadEFunction (f : ℂ → ℂ) : Prop :=
  ∃ a : ℕ → AlgebraicComplex,
    Differentiable ℂ f ∧
    (∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z)) ∧
    HasAlgebraicPolynomialODE f ∧ V5BroadAlgebraicArithmetic a

theorem v5_strict_arithmetic_is_broad (a : ℕ → AlgebraicComplex)
    (h : HasStrictEArithmetic a) : V5BroadAlgebraicArithmetic a := by
  obtain ⟨C,hC,hh,d,hd,hdb,hi⟩ := h
  intro ε hε
  have hfac (n : ℕ) : (1 : ℝ) ≤ (n.factorial : ℝ)^ε :=
    Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos n) hε.le
  exact ⟨C,hC,d,hd,fun n => (hdb n).trans (le_mul_of_one_le_right (by positivity) (hfac n)),
    fun σ n => (hh σ n).trans (le_mul_of_one_le_right (by positivity) (hfac n)),hi⟩

theorem v5_strict_is_broad {f : ℂ → ℂ} (h : IsStrictEFunction f) : V5IsBroadEFunction f := by
  obtain ⟨a,he,hs,ho,ha⟩ := h
  exact ⟨a,he,hs,ho,v5_strict_arithmetic_is_broad a ha⟩

/-- Transfer the actual series and algebraic polynomial equation together,
without assuming a formal equation in the definition of a broad E-function. -/
theorem v5_actual_broad_ode_data (f : entireFunctionAlgebra)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f.val z))
    (m : ℕ) (p : Fin (m+1) → Polynomial AlgebraicComplex)
    (hode : ∀ z : ℂ, ∑ i, (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
      iteratedDeriv i.val f.val z = 0) :
    (∀ n, (a n : ℂ) = v5FactorialCoeff (entireTaylorAlgHom f) n) ∧
    (∑ i, (p i : PowerSeries AlgebraicComplex) *
      (PowerSeries.derivative AlgebraicComplex)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))) = 0) := by
  let φ := (algebraicClosure ℚ ℂ).val.toRingHom
  let x : PowerSeries AlgebraicComplex :=
    PowerSeries.mk (fun n => a n / (n.factorial : AlgebraicComplex))
  have ht (n : ℕ) : PowerSeries.coeff ℂ n (entireTaylorAlgHom f) = (a n : ℂ)/(n.factorial : ℂ) := by
    rw [entireTaylorAlgHom_apply, coeff_entireFormalTaylor]
    apply entireCauchyCoefficient_eq_of_hasSum f.property
    intro z
    convert hs z using 1
    funext j
    ring
  have hx : PowerSeries.map φ x = entireTaylorAlgHom f := by
    ext n
    rw [ht]
    simp only [x, PowerSeries.coeff_map, PowerSeries.coeff_mk, map_div₀, map_natCast]
    rfl
  refine ⟨?_,?_⟩
  · intro n
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    rw [v5FactorialCoeff, ht, mul_comm (n.factorial : ℂ), div_mul_cancel₀ _ hn]
  change (∑ i, (p i : PowerSeries AlgebraicComplex) *
    (PowerSeries.derivative AlgebraicComplex)^[i.val] x) = 0
  apply PowerSeries.map_injective φ φ.injective
  rw [map_sum, map_zero]
  simp only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe, hx]
  let P : ℕ → Polynomial ℂ := fun j => if hj : j < m+1 then (p ⟨j,hj⟩).map φ else 0
  have hP (i : Fin (m+1)) : P i.val = (p i).map φ := dif_pos i.isLt
  have hr : ∀ z, v5RowResidual f.val m P z = 0 := by
    intro z
    rw [v5RowResidual, ← Fin.sum_univ_eq_sum_range]
    change (∑ i : Fin (m+1), (P i.val).eval z * iteratedDeriv i.val f.val z) = 0
    simpa only [hP, Polynomial.eval_map] using hode z
  have hf := (v5_formalRow_eq_zero_iff f P m).mpr hr
  rw [v5FormalRow, ← Fin.sum_univ_eq_sum_range] at hf
  simpa only [hP] using hf

#print axioms v5_strict_is_broad
#print axioms v5_actual_broad_ode_data
end StrictEUnit
end
