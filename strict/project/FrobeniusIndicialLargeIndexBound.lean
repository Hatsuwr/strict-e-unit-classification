import FourierTriangularCoefficientSupport

/-! A genuine large-index analytic estimate for the scalar indicial divisor.
The inverse of P(rho+n) decays with the full indicial degree. This does NOT yet
bound the inverse polynomial differential operator or prove convergence. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem complex_multiset_root_product_lower (s : Multiset ℂ) (z : ℂ) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ a ∈ s,c ≤ ‖z-a‖) :
    c^s.card ≤ ‖(s.map (fun a => z-a)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have hs := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    simp only [Multiset.card_cons,pow_succ,Multiset.map_cons,Multiset.prod_cons,norm_mul]
    rw [mul_comm]
    exact mul_le_mul ha hs (pow_nonneg hc _) (norm_nonneg _)

/-- The leading-degree lower bound is derived from the actual roots,
with multiplicities. No asymptotic bound is supplied as a hypothesis. -/
theorem complexPolynomial_eventually_eval_lower (P : Polynomial ℂ) (hP : P ≠ 0) (rho : ℂ) :
    ∃ N : ℕ,∃ c : ℝ,0<c ∧ ∀ n : ℕ,N≤n →
      c*((n : ℝ)+1)^P.natDegree ≤ ‖P.eval (rho+(n : ℂ))‖ := by
  let R : ℝ := ∑ a ∈ P.roots.toFinset,‖rho-a‖
  obtain ⟨N,hN⟩ := exists_nat_ge (2*R+1)
  have hlead : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨N,‖P.leadingCoeff‖/(2:ℝ)^P.natDegree,div_pos hlead (by positivity),?_⟩
  intro n hn
  have hnR : 2*R+1 ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hroot (a : ℂ) (ha : a ∈ P.roots) : ((n : ℝ)+1)/2 ≤ ‖rho+(n : ℂ)-a‖ := by
    have haR : ‖rho-a‖ ≤ R :=
      Finset.single_le_sum (fun b hb => norm_nonneg (rho-b)) (Multiset.mem_toFinset.mpr ha)
    have htri : (n : ℝ) ≤ ‖rho+(n : ℂ)-a‖+‖rho-a‖ := by
      have h := norm_sub_le (rho+(n : ℂ)-a) (rho-a)
      have he : (rho+(n : ℂ)-a)-(rho-a) = (n : ℂ) := by ring
      simpa only [he,Complex.norm_natCast] using h
    linarith
  have hprod := complex_multiset_root_product_lower P.roots (rho+(n : ℂ))
    (((n : ℝ)+1)/2) (by positivity) hroot
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits_codomain P
  have hcard : P.roots.card = P.natDegree := by
    simpa only [Polynomial.map_id] using (Polynomial.natDegree_eq_card_roots hsplit).symm
  rw [hcard] at hprod
  calc
    ‖P.leadingCoeff‖/(2:ℝ)^P.natDegree * ((n : ℝ)+1)^P.natDegree =
        ‖P.leadingCoeff‖ * (((n : ℝ)+1)/2)^P.natDegree := by rw [div_pow]; ring
    _ ≤ ‖P.leadingCoeff‖ * ‖(P.roots.map (fun a => rho+(n : ℂ)-a)).prod‖ :=
      mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖P.eval (rho+(n : ℂ))‖ := by
      rw [Polynomial.eval_eq_prod_roots_sub_of_splits_id hsplit,norm_mul]

/-- Actual nonvanishing and inverse decay beyond a derived finite cutoff.
The exact degree is retained, including the nonzero constant case. -/
theorem complexPolynomial_eventually_inverse_bound (P : Polynomial ℂ) (hP : P ≠ 0) (rho : ℂ) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      P.eval (rho+(n : ℂ)) ≠ 0 ∧
      ‖(P.eval (rho+(n : ℂ)))⁻¹‖ ≤ C/((n : ℝ)+1)^P.natDegree := by
  obtain ⟨N,c,hc,hbound⟩ := complexPolynomial_eventually_eval_lower P hP rho
  refine ⟨N,c⁻¹,inv_pos.mpr hc,?_⟩
  intro n hn
  have hd : 0 < ((n : ℝ)+1)^P.natDegree := pow_pos (by positivity) _
  have hpos : 0 < c*((n : ℝ)+1)^P.natDegree := mul_pos hc hd
  have he : 0 < ‖P.eval (rho+(n : ℂ))‖ := hpos.trans_le (hbound n hn)
  refine ⟨norm_pos_iff.mp he,?_⟩
  have hi := one_div_le_one_div_of_le hpos (hbound n hn)
  simpa only [one_div,norm_inv,mul_inv_rev,div_eq_mul_inv,mul_comm,one_mul] using hi

end StrictEUnit
end

#print axioms StrictEUnit.complex_multiset_root_product_lower
#print axioms StrictEUnit.complexPolynomial_eventually_eval_lower
#print axioms StrictEUnit.complexPolynomial_eventually_inverse_bound
