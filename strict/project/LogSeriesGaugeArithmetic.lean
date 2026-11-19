import LogPolynomialPrefixAlignment
import GeneralizedLogReflection

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

def LogSeriesPrefixArithmetic (u : LaurentSeries (Polynomial K)) : Prop :=
  ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
    ∀ m,m≤N →∀ t,IsIntegral ℤ ((D:K)*(u.coeff (m:ℤ)).coeff t)

/-- Fixed monomial gauges preserve full nonnegative-prefix arithmetic,
including the finite formerly-negative initial coefficients. -/
theorem logSeriesPrefixArithmetic_monomial (u : LaurentSeries (Polynomial K))
    (hu : LogSeriesPrefixArithmetic u) (k : ℤ) :
    LogSeriesPrefixArithmetic (HahnSeries.single k (1:Polynomial K)*u) := by
  obtain ⟨B,hB,hd⟩ := hu
  let v := HahnSeries.single k (1:Polynomial K)*u
  obtain ⟨E,hE,he⟩ := logPolynomial_tail_to_prefix
    (fun (_ : Unit) z =>v.coeff z) k B hB (by
      intro N
      obtain ⟨D,hD,hDb,hDi⟩ := hd N
      refine ⟨D,hD,hDb,?_⟩
      intro m hm i t
      dsimp [v]
      rw [HahnSeries.coeff_single_mul_add,one_mul]
      exact hDi m hm t)
  exact ⟨E,hE,fun N =>by
    obtain ⟨D,hD,hDb,hDi⟩ := he N
    exact ⟨D,hD,hDb,fun m hm t =>hDi m hm () t⟩⟩

theorem logSeriesPrefixArithmetic_reflection (u : LaurentSeries (Polynomial K))
    (hu : LogSeriesPrefixArithmetic u) : LogSeriesPrefixArithmetic (logLaurentReflection u) := by
  obtain ⟨B,hB,hd⟩ := hu
  refine ⟨B,hB,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hd N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm t
  change IsIntegral ℤ ((D:K)*(((-1:K)^(m:ℤ)) • u.coeff (m:ℤ)).coeff t)
  rw [Polynomial.coeff_smul,smul_eq_mul,zpow_natCast]
  have hi : IsIntegral ℤ ((-1:K)^m) := (isIntegral_one.neg).pow m
  convert hi.mul (hDi m hm t) using 1 <;> ring

/-- Undo the exact monomial/reflection/monomial gauge used for actual
reciprocal preimages, with no loss of initial or logarithmic coefficients. -/
theorem logSeriesPrefixArithmetic_undo_reflected_gauge
    (u : LaurentSeries (Polynomial K)) (k g : ℤ)
    (h : LogSeriesPrefixArithmetic (HahnSeries.single k (1:Polynomial K)*
      logLaurentReflection (HahnSeries.single g (1:Polynomial K)*u))) :
    LogSeriesPrefixArithmetic u := by
  have h1 := logSeriesPrefixArithmetic_monomial _ h (-k)
  simp only [← mul_assoc,HahnSeries.single_mul_single,neg_add_cancel,one_mul,
    HahnSeries.single_zero_one] at h1
  have h2 := logSeriesPrefixArithmetic_reflection _ h1
  rw [logLaurentReflection_involutive] at h2
  have h3 := logSeriesPrefixArithmetic_monomial _ h2 (-g)
  simpa only [← mul_assoc,HahnSeries.single_mul_single,neg_add_cancel,one_mul,
    HahnSeries.single_zero_one] using h3

end StrictEUnit
end
