import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Finiteness.Basic

/-! Strict total-degree lowering relations imply finite generation of the
actual polynomial quotient. No bounded-span or finite-dimensional premise. -/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
open MvPolynomial
variable {k ι : Type*} [CommRing k] [Fintype ι]

omit [Fintype ι] in
lemma quotient_polynomial_mem_of_monomials (I : Ideal (MvPolynomial ι k))
    (S : Submodule k (MvPolynomial ι k ⧸ I)) (p : MvPolynomial ι k)
    (h : ∀ d ∈ p.support, Ideal.Quotient.mk I (monomial d (1:k)) ∈ S) :
    Ideal.Quotient.mk I p ∈ S := by
  classical
  rw [p.as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hs := S.smul_mem (p.coeff d) (h d hd)
  change (Ideal.Quotient.mkₐ k I) (monomial d (p.coeff d)) ∈ S
  rw [show monomial d (p.coeff d) = p.coeff d • monomial d (1:k) by rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul]
  exact hs

/-- A finite family of bounded monomials spans the quotient under genuinely
strict degree-lowering equations for each variable. -/
theorem quotient_span_bounded_monomials (I : Ideal (MvPolynomial ι k))
    (N : ι → ℕ) (q : ι → MvPolynomial ι k)
    (hq : ∀ i, (q i).totalDegree < N i)
    (hrel : ∀ i, X i ^ N i - q i ∈ I) :
    Submodule.span k (Set.range (fun d : (i : ι) → Fin (N i) =>
      Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm (fun i => (d i).val)) (1:k)))) = ⊤ := by
  classical
  let S : Submodule k (MvPolynomial ι k ⧸ I) := Submodule.span k
    (Set.range (fun d : (i : ι) → Fin (N i) =>
      Ideal.Quotient.mk I (monomial (Finsupp.equivFunOnFinite.symm (fun i => (d i).val)) (1:k))))
  have hmono : ∀ t : ℕ, ∀ d : ι →₀ ℕ, d.sum (fun _ n => n) = t →
      Ideal.Quotient.mk I (monomial d (1:k)) ∈ S := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro d hd
      by_cases hb : ∀ i, d i < N i
      · apply Submodule.subset_span
        refine ⟨fun i => ⟨d i, hb i⟩, ?_⟩
        change Ideal.Quotient.mk I (monomial
          (Finsupp.equivFunOnFinite.symm (Finsupp.equivFunOnFinite d)) (1:k)) = _
        rw [Finsupp.equivFunOnFinite.symm_apply_apply]
      · obtain ⟨i, hi⟩ := not_forall.mp hb
        have hNi : N i ≤ d i := Nat.le_of_not_gt hi
        let e := d - Finsupp.single i (N i)
        have hle : Finsupp.single i (N i) ≤ d := by
          intro j
          by_cases hj : i = j
          · subst j; simpa using hNi
          · simp [Finsupp.single_eq_of_ne hj]
        have he : e + Finsupp.single i (N i) = d := tsub_add_cancel_of_le hle
        have hsum : e.sum (fun _ n => n) + N i = t := by
          rw [← hd, ← he]
          simp [Finsupp.sum_add_index]
        let p : MvPolynomial ι k := monomial e 1 * q i
        have hpdeg : p.totalDegree < t := by
          have hh := totalDegree_mul (monomial e (1:k)) (q i)
          have hm := totalDegree_monomial_le e (1:k)
          dsimp [p]
          exact lt_of_le_of_lt hh (lt_of_le_of_lt (Nat.add_le_add_right hm _)
            (by simpa [hsum] using Nat.add_lt_add_left (hq i) (e.sum (fun _ n => n))))
        have hp : Ideal.Quotient.mk I p ∈ S := by
          apply quotient_polynomial_mem_of_monomials I S p
          intro s hs
          exact ih (s.sum (fun _ n => n)) (lt_of_le_of_lt (le_totalDegree hs) hpdeg) s rfl
        have hqi : Ideal.Quotient.mk I (X i ^ N i) = Ideal.Quotient.mk I (q i) := by
          apply sub_eq_zero.mp
          rw [← map_sub]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (hrel i)
        have heq : Ideal.Quotient.mk I (monomial d (1:k)) = Ideal.Quotient.mk I p := by
          rw [← he, ← one_mul (1:k), ← monomial_mul, ← X_pow_eq_monomial, map_mul, hqi]
          rfl
        exact heq.symm ▸ hp
  apply top_unique
  intro x hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact quotient_polynomial_mem_of_monomials I S p (fun d _ => hmono _ d rfl)

/-- The quotient is a finite k-module, over any commutative coefficient ring. -/
theorem finite_quotient_of_degree_lowering (I : Ideal (MvPolynomial ι k))
    (N : ι → ℕ) (q : ι → MvPolynomial ι k)
    (hq : ∀ i, (q i).totalDegree < N i)
    (hrel : ∀ i, X i ^ N i - q i ∈ I) :
    Module.Finite k (MvPolynomial ι k ⧸ I) := by
  classical
  apply Module.finite_def.mpr
  rw [← quotient_span_bounded_monomials I N q hq hrel]
  exact Submodule.fg_span (Set.finite_range _)
end StrictEUnit
#print axioms StrictEUnit.quotient_polynomial_mem_of_monomials
#print axioms StrictEUnit.quotient_span_bounded_monomials
#print axioms StrictEUnit.finite_quotient_of_degree_lowering
