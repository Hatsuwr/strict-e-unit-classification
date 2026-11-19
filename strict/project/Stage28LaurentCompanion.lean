import Stage15StrictEDerivativeClosure
import Stage27ZeroFrame

/-! A literal ordinary polynomial ODE with monomial leading coefficient gives
an actual Laurent Euler companion system. No vector equation is an input. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators
namespace StrictEUnit

/-- An actual ordinary scalar equation on the whole complex plane, with an
explicitly nonzero monomial leading coefficient. Positive order is separate. -/
structure Stage28MonomialLeadingODE (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ) : Prop where
  coefficient_ne_zero : c ≠ 0
  leading : p (Fin.last m) = Polynomial.monomial r c
  equation : ∀ z : ℂ, ∑ j, (p j).eval₂ k.subtype z * iteratedDeriv j.val f z = 0

/-- The displayed equation is genuinely a nonzero polynomial ODE in the
existing analytic predicate; monomial nonvanishing is not merely a name. -/
theorem stage28_hasSubfieldPolynomialODE (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ)
    (h : Stage28MonomialLeadingODE k m r c p f) : HasSubfieldPolynomialODE k f := by
  refine ⟨m, p, ⟨Fin.last m, ?_⟩, h.equation⟩
  rw [h.leading]
  exact fun hz => h.coefficient_ne_zero ((Polynomial.monomial_eq_zero_iff c r).mp hz)

/-- The ordinary derivative jet, not an assumed solution vector. -/
def stage28_derivativeJet (m : ℕ) (f : ℂ → ℂ) : Fin m → ℂ → ℂ :=
  fun i => iteratedDeriv i.val f

/-- z times the ordinary companion matrix. The final row lies in the literal
finite Laurent polynomial ring, including when the leading exponent exceeds 1. -/
def stage28_laurentCompanion (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) : Matrix (Fin m) (Fin m) (LaurentPolynomial k) :=
  fun i j => if i.val + 1 < m then
    if j.val = i.val + 1 then LaurentPolynomial.T 1 else 0
  else -(LaurentPolynomial.C c⁻¹ * LaurentPolynomial.T (1 - (r : ℤ)) *
    Polynomial.toLaurent (p j.castSucc))

/-- Exact evaluated entries of the constructed matrix. Laurent evaluation is
only at units, so a negative power is never evaluated at the origin. -/
theorem stage28_laurentCompanion_eval (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (z : ℂˣ) (i j : Fin m) :
    LaurentPolynomial.eval₂ k.subtype z (stage28_laurentCompanion k m r c p i j) =
      if i.val + 1 < m then (if j.val = i.val + 1 then (z : ℂ) else 0)
      else -((c : ℂ)⁻¹ * (z : ℂ) ^ (1 - (r : ℤ)) *
        (p j.castSucc).eval₂ k.subtype (z : ℂ)) := by
  unfold stage28_laurentCompanion
  split_ifs <;> simp [LaurentPolynomial.eval₂_T, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_toLaurent]

/-- The final scalar differential relation after separating its top derivative. -/
theorem stage28_scalarODE_last (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ)
    (h : Stage28MonomialLeadingODE k m r c p f) (z : ℂ) :
    (∑ j : Fin m, (p j.castSucc).eval₂ k.subtype z * iteratedDeriv j.val f z) +
      (c : ℂ) * z ^ r * iteratedDeriv m f z = 0 := by
  have he := h.equation z
  rw [Fin.sum_univ_castSucc, h.leading] at he
  simpa only [Fin.coe_castSucc, Fin.val_last, Polynomial.eval₂_monomial] using he

/-- The Laurent multiplier cancels the nonzero monomial at every punctured point. -/
theorem stage28_leading_cancel (k : Subfield ℂ) (r : ℕ) (c : k) (hc : c ≠ 0)
    (z : ℂˣ) :
    ((c : ℂ)⁻¹ * (z : ℂ) ^ (1 - (r : ℤ))) * ((c : ℂ) * (z : ℂ)^r) = z := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hz : (z : ℂ) ^ (1 - (r : ℤ)) * (z : ℂ)^r = (z : ℂ) := by
    rw [← zpow_natCast, ← zpow_add₀ z.ne_zero]
    simp
  calc
    _ = ((c : ℂ)⁻¹ * (c : ℂ)) *
      ((z : ℂ) ^ (1 - (r : ℤ)) * (z : ℂ)^r) := by ring
    _ = z := by rw [inv_mul_cancel₀ hc', one_mul, hz]

/-- The constructed derivative jet solves the constructed Laurent Euler system.
There is no assumed solution equation, formal-series substitute, or closure input. -/
theorem stage28_derivativeJet_solution (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ)
    (h : Stage28MonomialLeadingODE k m r c p f) :
    Stage27ActualEulerSolution k (stage28_laurentCompanion k m r c p)
      (stage28_derivativeJet m f) := by
  intro z i
  simp only [stage28_derivativeJet, ← iteratedDeriv_succ]
  simp_rw [stage28_laurentCompanion_eval]
  by_cases hi : i.val + 1 < m
  · let j : Fin m := ⟨i.val + 1, hi⟩
    have hj (l : Fin m) : l.val = i.val + 1 ↔ l = j := by
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [hi, if_true, hj, ite_mul, zero_mul]
    simp [j]
  · have him : i.val + 1 = m := by omega
    simp only [hi, if_false]
    rw [him]
    have he := stage28_scalarODE_last k m r c p f h (z : ℂ)
    let q : ℂ := (c : ℂ)⁻¹ * (z : ℂ) ^ (1 - (r : ℤ))
    have hc : q * ((c : ℂ) * (z : ℂ)^r) = z :=
      stage28_leading_cancel k r c h.coefficient_ne_zero z
    have ht := congrArg (fun x : ℂ => q * x) he
    dsimp only at ht
    rw [mul_add, ← mul_assoc, hc, mul_zero] at ht
    have hs : ∑ l : Fin m,
        -(q * (p l.castSucc).eval₂ k.subtype (z : ℂ)) * iteratedDeriv l.val f (z : ℂ) =
        -(q * ∑ l : Fin m,
          (p l.castSucc).eval₂ k.subtype (z : ℂ) * iteratedDeriv l.val f (z : ℂ)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [hs]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using ht)

/-- Every component has the full strict-E predicate, by proved derivative closure. -/
theorem stage28_derivativeJet_strict {f : ℂ → ℂ} (hf : IsStrictEFunction f) (m : ℕ) :
    ∀ i : Fin m, IsStrictEFunction (stage28_derivativeJet m f i) :=
  fun i => strictEFunction_iteratedDeriv hf i.val

/-- Positive order supplies a literal copy of f in component zero. -/
theorem stage28_derivativeJet_zero (m : ℕ) (hm : 0 < m) (f : ℂ → ℂ) :
    stage28_derivativeJet m f ⟨0, hm⟩ = f := by
  simp [stage28_derivativeJet]

/-- Positive-order scalar input supplies all solution-vector and original
component obligations independently of any normal-form frame existence. -/
theorem stage28_exists_strictE_companion (k : Subfield ℂ) (m r : ℕ) (c : k)
    (p : Fin (m + 1) → Polynomial k) (f : ℂ → ℂ) (hf : IsStrictEFunction f)
    (h : Stage28MonomialLeadingODE k m r c p f) (hm : 0 < m) :
    ∃ v : Fin m → ℂ → ℂ, (∀ i, IsStrictEFunction (v i)) ∧
      Stage27ActualEulerSolution k (stage28_laurentCompanion k m r c p) v ∧
      v ⟨0, hm⟩ = f :=
  ⟨stage28_derivativeJet m f, stage28_derivativeJet_strict hf m,
    stage28_derivativeJet_solution k m r c p f h, stage28_derivativeJet_zero m hm f⟩

end StrictEUnit
