import LaurentLogLeibniz
import Mathlib.Order.WellFounded

noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k] [CharZero k]

/-- A minimal-support nonzero stable-ideal element has only one Laurent mode. -/
theorem laurentLog_minimal_support_single
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, laurentLogD f ∈ I)
    (f : LaurentPolynomial (Polynomial k)) (hf : f ∈ I) (hf0 : f ≠ 0)
    (hmin : ∀ g ∈ I, g ≠ 0 → f.support.card ≤ g.support.card) :
    ∃ n : ℤ, f.support ⊆ {n} := by
  obtain ⟨n, hn⟩ := Finsupp.support_nonempty_iff.mpr hf0
  refine ⟨n, ?_⟩
  intro m hm
  apply Finset.mem_singleton.mpr
  by_contra hmn
  let j := (f n).natDegree + 1
  let g := (laurentLogShift (n : k))^[j] f
  have hgI : g ∈ I := laurentLogShift_stable_ideal I hI _ f hf j
  have hgn : g n = 0 := by
    rw [laurentLogShift_iterate_coeff, sub_self]
    rw [show shiftedPolynomialDerivative (0 : k) = Polynomial.derivative by
      simp [shiftedPolynomialDerivative]]
    exact Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self _)
  have hgm : g m ≠ 0 := by
    rw [laurentLogShift_iterate_coeff]
    apply shiftedPolynomialDerivative_iterate_ne_zero _ _ _ (Finsupp.mem_support_iff.mp hm)
    exact sub_ne_zero.mpr (by exact_mod_cast hmn)
  have hg0 : g ≠ 0 := by intro h; apply hgm; rw [h]; rfl
  have hsub : g.support ⊆ f.support.erase n := by
    intro i hi
    apply Finset.mem_erase.mpr
    refine ⟨?_, laurentLogShift_iterate_support_subset (n : k) f j hi⟩
    intro hin
    subst i
    exact Finsupp.mem_support_iff.mp hi hgn
  have hlt : g.support.card < f.support.card :=
    lt_of_le_of_lt (Finset.card_le_card hsub) (Finset.card_erase_lt_of_mem hn)
  exact (Nat.not_lt_of_ge (hmin g hgI hg0)) hlt

/-- Every nonzero stable ideal contains a nonzero single Laurent mode. -/
theorem laurentLog_stable_contains_single
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, laurentLogD f ∈ I) (hI0 : I ≠ ⊥) :
    ∃ n : ℤ, ∃ p : Polynomial k, p ≠ 0 ∧ Finsupp.single n p ∈ I := by
  obtain ⟨f, hfI, hf0⟩ := (Submodule.ne_bot_iff I).mp hI0
  obtain ⟨g, ⟨hgI, hg0⟩, hmin⟩ :=
    (measure (fun f : LaurentPolynomial (Polynomial k) => f.support.card)).wf.has_min
      {f | f ∈ I ∧ f ≠ 0} ⟨f, hfI, hf0⟩
  obtain ⟨n, hn⟩ := laurentLog_minimal_support_single I hI g hgI hg0
    (by intro h hh hh0; exact Nat.le_of_not_lt (hmin h ⟨hh, hh0⟩))
  have he : g = Finsupp.single n (g n) := Finsupp.support_subset_singleton.mp hn
  refine ⟨n, g n, ?_, he ▸ hgI⟩
  intro hz
  apply hg0
  rw [he, hz, Finsupp.single_zero]

/-- The top nonzero derivative of a polynomial is a nonzero constant. -/
theorem polynomial_top_derivative_constant (p : Polynomial k) (hp : p ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ Polynomial.derivative^[p.natDegree] p = Polynomial.C c := by
  let q := Polynomial.derivative^[p.natDegree] p
  have hq : q.natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    simpa using Polynomial.natDegree_iterate_derivative p p.natDegree
  refine ⟨q.coeff 0, ?_, ?_⟩
  · change (Polynomial.derivative^[p.natDegree] p).coeff 0 ≠ 0
    rw [Polynomial.coeff_iterate_derivative, zero_add, Nat.descFactorial_self,
      Polynomial.coeff_natDegree, nsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero p.natDegree)
      (Polynomial.leadingCoeff_ne_zero.mpr hp)
  · simpa only [Polynomial.coeff_zero_eq_eval_zero] using
      Polynomial.eq_C_of_natDegree_eq_zero hq

/-- The actual Laurent-plus-logarithm operator has no nontrivial stable ideals. -/
theorem laurentLog_stable_ideal_eq_top
    (I : Ideal (LaurentPolynomial (Polynomial k)))
    (hI : ∀ f ∈ I, laurentLogD f ∈ I) (hI0 : I ≠ ⊥) : I = ⊤ := by
  obtain ⟨n, p, hp, hnp⟩ := laurentLog_stable_contains_single I hI hI0
  obtain ⟨c, hc, hpc⟩ := polynomial_top_derivative_constant p hp
  have hg := laurentLogShift_stable_ideal I hI (n : k)
    (Finsupp.single n p) hnp p.natDegree
  have he : (laurentLogShift (n : k))^[p.natDegree] (Finsupp.single n p) =
      Finsupp.single n (Polynomial.C c) := by
    apply Finsupp.ext
    intro m
    rw [laurentLogShift_iterate_coeff]
    by_cases hmn : m = n
    · subst m
      simp only [Finsupp.single_eq_same, sub_self]
      rw [show shiftedPolynomialDerivative (0 : k) = Polynomial.derivative by
        simp [shiftedPolynomialDerivative]]
      exact hpc
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hmn), iterate_map_zero]
  rw [he] at hg
  apply Ideal.eq_top_of_isUnit_mem I hg
  apply isUnit_of_mul_eq_one (M := LaurentPolynomial (Polynomial k))
    (Finsupp.single n (Polynomial.C c) : LaurentPolynomial (Polynomial k))
    (Finsupp.single (-n) (Polynomial.C c⁻¹) : LaurentPolynomial (Polynomial k))
  rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, ← Polynomial.C_mul,
    mul_inv_cancel₀ hc, Polynomial.C_1]
  exact AddMonoidAlgebra.one_def.symm
end StrictEUnit

#print axioms StrictEUnit.laurentLog_minimal_support_single
#print axioms StrictEUnit.laurentLog_stable_contains_single


#print axioms StrictEUnit.polynomial_top_derivative_constant
#print axioms StrictEUnit.laurentLog_stable_ideal_eq_top
