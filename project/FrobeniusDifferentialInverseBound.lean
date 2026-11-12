import FrobeniusBoundedLogSize

/-! The full logarithmic differential inverse, on any fixed log-degree window,
has the full indicial inverse decay. The proof uses the actual complex root
factorization and bounds every first-order factor, not just its scalar diagonal. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem shiftedPolynomialDifferentialOperator_linearFactor (c a : ℂ) (f : Polynomial ℂ) :
    shiftedPolynomialDifferentialOperator c (Polynomial.X-Polynomial.C a) f =
      shiftedPolynomialDerivative (c-a) f := by
  simp only [shiftedPolynomialDifferentialOperator,map_sub,Polynomial.aeval_X,
    Polynomial.aeval_C,LinearMap.sub_apply,Module.algebraMap_end_apply,
    shiftedPolynomialDerivative_apply,sub_smul]
  abel

theorem polynomialLogSize_root_product_lower (d : ℕ) (s : Multiset ℂ) (c : ℂ)
    (a : ℝ) (ha : 0 ≤ a) (h : ∀ z ∈ s,a+((d : ℝ)+1)^2 ≤ ‖c-z‖)
    (f : Polynomial ℂ) (hf : f.natDegree ≤ d) :
    a^s.card*polynomialLogSize d f ≤
      polynomialLogSize d (shiftedPolynomialDifferentialOperator c
        ((s.map (fun z => Polynomial.X-Polynomial.C z)).prod) f) := by
  induction s using Multiset.induction_on with
  | empty => simp [shiftedPolynomialDifferentialOperator]
  | @cons z s ih =>
    let q := shiftedPolynomialDifferentialOperator c
      ((s.map (fun z => Polynomial.X-Polynomial.C z)).prod) f
    have hq : q.natDegree ≤ d := (shiftedPolynomialDifferentialOperator_natDegree_le _ _ _).trans hf
    have hz := h z (Multiset.mem_cons_self z s)
    have hs := ih (fun b hb => h b (Multiset.mem_cons_of_mem hb))
    have hl := polynomialLogSize_shiftedDerivative_lower d (c-z) q hq
    have hfirst : a*polynomialLogSize d q ≤ polynomialLogSize d (shiftedPolynomialDerivative (c-z) q) :=
      (mul_le_mul_of_nonneg_right (by linarith : a ≤ ‖c-z‖-((d : ℝ)+1)^2)
        (polynomialLogSize_nonneg d q)).trans hl
    simp only [Multiset.card_cons,pow_succ,Multiset.map_cons,Multiset.prod_cons]
    have he : shiftedPolynomialDifferentialOperator c
        ((Polynomial.X-Polynomial.C z)*(s.map (fun z => Polynomial.X-Polynomial.C z)).prod) f =
        shiftedPolynomialDerivative (c-z) q := by
      rw [shiftedPolynomialDifferentialOperator, map_mul,Module.End.mul_apply]
      exact shiftedPolynomialDifferentialOperator_linearFactor c z q
    rw [he,mul_right_comm]
    simpa only [mul_comm a] using (mul_le_mul_of_nonneg_left hs ha).trans hfirst

/-- A derived lower bound for the entire differential operator. -/
theorem complexPolynomial_eventually_differential_lower (P : Polynomial ℂ)
    (hP : P ≠ 0) (rho : ℂ) (d : ℕ) :
    ∃ N : ℕ,∃ c : ℝ,0<c ∧ ∀ n : ℕ,N≤n → ∀ f : Polynomial ℂ,f.natDegree≤d →
      c*((n : ℝ)+1)^P.natDegree*polynomialLogSize d f ≤
        polynomialLogSize d (shiftedPolynomialDifferentialOperator (rho+(n : ℂ)) P f) := by
  let R : ℝ := ∑ a ∈ P.roots.toFinset,‖rho-a‖
  let D : ℝ := ((d : ℝ)+1)^2
  obtain ⟨N,hN⟩ := exists_nat_ge (2*R+4*D+1)
  have hlead : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨N,‖P.leadingCoeff‖/(4:ℝ)^P.natDegree,div_pos hlead (by positivity),?_⟩
  intro n hn f hf
  have hR : 0 ≤ R := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hD : 0 ≤ D := sq_nonneg _
  have hnR : 2*R+4*D+1 ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hroot (a : ℂ) (ha : a ∈ P.roots) : ((n : ℝ)+1)/4+((d : ℝ)+1)^2 ≤ ‖rho+(n : ℂ)-a‖ := by
    have haR : ‖rho-a‖ ≤ R :=
      Finset.single_le_sum (fun b hb => norm_nonneg (rho-b)) (Multiset.mem_toFinset.mpr ha)
    have htri : (n : ℝ) ≤ ‖rho+(n : ℂ)-a‖+‖rho-a‖ := by
      have h := norm_sub_le (rho+(n : ℂ)-a) (rho-a)
      have he : (rho+(n : ℂ)-a)-(rho-a) = (n : ℂ) := by ring
      simpa only [he,Complex.norm_natCast] using h
    change ((n : ℝ)+1)/4+D ≤ _
    linarith
  have hprod := polynomialLogSize_root_product_lower d P.roots (rho+(n : ℂ))
    (((n : ℝ)+1)/4) (by positivity) hroot f hf
  have hsplit : P.Splits (RingHom.id ℂ) := IsAlgClosed.splits_codomain P
  have hcard : P.roots.card = P.natDegree := by
    simpa only [Polynomial.map_id] using (Polynomial.natDegree_eq_card_roots hsplit).symm
  rw [hcard] at hprod
  have he : shiftedPolynomialDifferentialOperator (rho+(n : ℂ)) P f =
      P.leadingCoeff • shiftedPolynomialDifferentialOperator (rho+(n : ℂ))
        ((P.roots.map (fun a => Polynomial.X-Polynomial.C a)).prod) f := by
    conv_lhs => rw [Polynomial.eq_prod_roots_of_splits_id hsplit]
    simp only [shiftedPolynomialDifferentialOperator,map_mul,Polynomial.aeval_C,
      Module.End.mul_apply,Module.algebraMap_end_apply]
  rw [he,polynomialLogSize_smul]
  calc
    _ = ‖P.leadingCoeff‖ * ((((n : ℝ)+1)/4)^P.natDegree*polynomialLogSize d f) := by rw [div_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)

/-- The EXISTING canonical logarithmic right inverse satisfies the estimate.
Only the ordinary hypotheses P≠0 and a finite log window are used. -/
theorem complexPolynomial_eventually_differential_inverse_bound (P : Polynomial ℂ)
    (hP : P ≠ 0) (rho : ℂ) (d : ℕ) :
    ∃ N : ℕ,∃ C : ℝ,0<C ∧ ∀ n : ℕ,N≤n →
      P.eval (rho+(n : ℂ)) ≠ 0 ∧
      ∀ f : Polynomial ℂ,f.natDegree≤d →
      polynomialLogSize d (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) P f) ≤
        C/((n : ℝ)+1)^P.natDegree*polynomialLogSize d f := by
  obtain ⟨N,c,hc,hlower⟩ := complexPolynomial_eventually_differential_lower P hP rho d
  obtain ⟨N₀,C₀,hC₀,hscalar⟩ := complexPolynomial_eventually_inverse_bound P hP rho
  refine ⟨max N N₀,c⁻¹,inv_pos.mpr hc,?_⟩
  intro n hn
  have hnonzero := (hscalar n (le_trans (le_max_right _ _) hn)).1
  refine ⟨hnonzero,?_⟩
  intro f hf
  have hm : P.rootMultiplicity (rho+(n : ℂ)) = 0 := Polynomial.rootMultiplicity_eq_zero hnonzero
  have hdeg : (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) P f).natDegree ≤ d := by
    have h := shiftedPolynomialDifferentialRightInverse_natDegree_le (rho+(n : ℂ)) P f
    rw [hm,add_zero] at h
    exact h.trans hf
  have h := hlower n (le_trans (le_max_left _ _) hn) _ hdeg
  rw [shiftedPolynomialDifferentialRightInverse_apply _ _ _ hP] at h
  have hx : 0 < ((n : ℝ)+1)^P.natDegree := pow_pos (by positivity) _
  have he : c⁻¹/((n : ℝ)+1)^P.natDegree*polynomialLogSize d f =
      polynomialLogSize d f/(c*((n : ℝ)+1)^P.natDegree) := by ring
  rw [he]
  exact (le_div_iff₀ (mul_pos hc hx)).mpr (by simpa only [mul_comm] using h)

end StrictEUnit
end
