import TensorClearedSystem
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.BigOperators.Fin

/-!
Every homogeneous polynomial is the exact substitution of a linear polynomial
in redundant tensor-word variables. No field, division, finite variable type,
positive degree, or nonzero-polynomial assumption is needed.

Source draft only. No compiler or kernel acceptance is claimed here.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit

variable {ι R : Type*} [CommSemiring R]

/-- A degree-D exponent vector has a word of length D with exactly its
multiplicities. The resulting monomial has coefficient one. -/
theorem exists_tensorWordMonomial (D : ℕ) (d : ι →₀ ℕ)
    (hd : d.degree = D) :
    ∃ w : Fin D → ι, tensorWordMonomial (R := R) D w =
      MvPolynomial.monomial d 1 := by
  classical
  let l := d.toMultiset.toList
  have hl : l.length = D := by
    calc
      l.length = d.toMultiset.card := Multiset.length_toList _
      _ = d.sum (fun _ => id) := Finsupp.card_toMultiset _
      _ = D := hd
  rw [← hl]
  refine ⟨fun k => l[k.val], ?_⟩
  change (∏ k : Fin l.length, MvPolynomial.X (R := R) l[k.val]) = _
  rw [Fin.prod_univ_fun_getElem]
  calc
    (l.map (MvPolynomial.X (R := R))).prod =
        (d.toMultiset.map (MvPolynomial.X (R := R))).prod := by
      simpa only [l, Multiset.map_coe, Multiset.prod_coe] using
        congrArg (fun s : Multiset ι =>
          (s.map (MvPolynomial.X (R := R))).prod)
          (Multiset.coe_toList d.toMultiset)
    _ = (d.mapDomain (MvPolynomial.X (R := R))).prod (fun p n => p ^ n) := by
      rw [Finsupp.toMultiset_map, Finsupp.prod_toMultiset]
    _ = d.prod (fun i n => MvPolynomial.X (R := R) i ^ n) :=
      Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)
    _ = MvPolynomial.monomial d 1 := MvPolynomial.prod_X_pow_eq_monomial

/-- Literal homogeneous-to-linear reduction. Duplicate tensor-word variables
are allowed, and exact substitution recovers P rather than a scalar multiple. -/
theorem homogeneous_exists_tensorWord_linearization (D : ℕ)
    (P : MvPolynomial ι R) (hP : P.IsHomogeneous D) :
    ∃ L : MvPolynomial (Fin D → ι) R,
      L.IsHomogeneous 1 ∧ tensorWordSubstitution D L = P := by
  classical
  have hdegree : ∀ d ∈ P.support, d.degree = D := by
    intro d hd
    by_contra hne
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hne)
  have hwords : ∀ d : P.support,
      ∃ w : Fin D → ι, tensorWordMonomial (R := R) D w =
        MvPolynomial.monomial d.val 1 := by
    intro d
    exact exists_tensorWordMonomial D d.val (hdegree d.val d.property)
  choose w hw using hwords
  let L : MvPolynomial (Fin D → ι) R :=
    ∑ d : P.support, MvPolynomial.C (P.coeff d.val) * MvPolynomial.X (w d)
  refine ⟨L, ?_, ?_⟩
  · exact MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun d : P.support => MvPolynomial.C (P.coeff d.val) * MvPolynomial.X (w d))
      1
      (fun d _ => MvPolynomial.isHomogeneous_C_mul_X _ _)
  · change tensorWordSubstitution D
        (∑ d : P.support, MvPolynomial.C (P.coeff d.val) * MvPolynomial.X (w d)) = P
    rw [map_sum]
    calc
      (∑ d : P.support, tensorWordSubstitution D
        (MvPolynomial.C (P.coeff d.val) * MvPolynomial.X (w d))) =
          ∑ d : P.support, MvPolynomial.monomial d.val (P.coeff d.val) := by
        apply Finset.sum_congr rfl
        intro d hd
        simp only [tensorWordSubstitution, map_mul, MvPolynomial.eval₂Hom_C,
          MvPolynomial.eval₂Hom_X', hw d, MvPolynomial.C_mul_monomial, mul_one]
      _ = ∑ d ∈ P.support, MvPolynomial.monomial d (P.coeff d) :=
        Finset.sum_coe_sort P.support (fun d => MvPolynomial.monomial d (P.coeff d))
      _ = P := MvPolynomial.support_sum_monomial_coeff P

end StrictEUnit
