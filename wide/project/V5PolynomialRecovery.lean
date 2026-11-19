import Mathlib.LinearAlgebra.Lagrange
import Mathlib.FieldTheory.IsAlgClosed.Basic

noncomputable section
open Polynomial
namespace StrictEUnit

/-- A root in an extension of an algebraically closed field of a nonzero
polynomial over the base is already the image of an element of the base. -/
theorem v5_root_in_algebraically_closed_base {k K : Type*}
    [Field k] [Field K] [IsAlgClosed k] (f : k →+* K)
    {p : Polynomial k} (hp : p ≠ 0) {x : K} (hx : p.eval₂ f x = 0) :
    ∃ y : k, f y = x := by
  have hm : x ∈ (p.map f).roots := mem_roots'.mpr
    ⟨Polynomial.map_ne_zero hp, (eval_map f x).trans hx⟩
  rw [Polynomial.roots_map f (IsAlgClosed.splits_codomain p)] at hm
  obtain ⟨y, _, hy⟩ := Multiset.mem_map.mp hm
  exact ⟨y, hy⟩

/-- Enough distinct scalar evaluations of a polynomial in the image of the
base field give an exact polynomial over the base, by interpolation. -/
theorem v5_polynomial_of_scalar_evaluations {k K ι : Type*}
    [Field k] [Field K] [DecidableEq ι] (f : k →+* K)
    (s : Finset ι) (v r : ι → k) (hv : Set.InjOn v (s : Set ι))
    (P : Polynomial K) (hd : P.degree < s.card)
    (hP : ∀ i ∈ s, P.eval (f (v i)) = f (r i)) :
    ∃ Q : Polynomial k, Q.map f = P := by
  let Q := Lagrange.interpolate s v r
  refine ⟨Q, ?_⟩
  have hfv : Set.InjOn (f ∘ v) (s : Set ι) := fun _ hi _ hj h =>
    hv hi hj (f.injective h)
  have hQ : (Q.map f).degree < s.card := by
    rw [degree_map_eq_of_injective f.injective]
    exact Lagrange.degree_interpolate_lt r hv
  refine eq_of_degrees_lt_of_eval_index_eq s hfv hQ hd (fun i hi => ?_)
  change (Q.map f).eval (f (v i)) = P.eval (f (v i))
  rw [hP i hi, eval_map, eval₂_hom]
  exact congrArg f (Lagrange.eval_interpolate_at_node r hv hi)

/-- If a cleared Laurent numerator is known at all nonzero natural nodes
by evaluating a Laurent function whose values satisfy nonzero equations
over the algebraically closed base, its coefficients descend to the base. -/
theorem v5_polynomial_of_monic_laurent_samples {k K : Type*}
    [Field k] [CharZero k] [Field K] [IsAlgClosed k] (f : k →+* K)
    (P : Polynomial K) (N : ℕ) (g : K → K)
    (hP : ∀ a : k, a ≠ 0 → P.eval (f a) = (f a)^N * g (f a))
    (hg : ∀ a : k, a ≠ 0 → ∃ p : Polynomial k, p.Monic ∧ p.eval₂ f (g (f a)) = 0) :
    ∃ Q : Polynomial k, Q.map f = P := by
  let d := P.natDegree + 1
  let v : Fin d → k := fun i => ((i.val + 1 : ℕ) : k)
  have hv0 (i : Fin d) : v i ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hv : Function.Injective v := by
    intro i j h
    apply Fin.ext
    exact Nat.add_right_cancel (Nat.cast_injective (R := k) h)
  have hs (i : Fin d) : ∃ y : k, f y = P.eval (f (v i)) := by
    obtain ⟨p, hp, he⟩ := hg (v i) (hv0 i)
    obtain ⟨y, hy⟩ := v5_root_in_algebraically_closed_base f hp.ne_zero he
    refine ⟨v i ^ N * y, ?_⟩
    rw [map_mul, map_pow, hy, hP (v i) (hv0 i)]
  choose r hr using hs
  apply v5_polynomial_of_scalar_evaluations f Finset.univ v r hv.injOn P
  · rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self _))
  · intro i _
    exact (hr i).symm

end StrictEUnit
#print axioms StrictEUnit.v5_root_in_algebraically_closed_base
#print axioms StrictEUnit.v5_polynomial_of_scalar_evaluations
#print axioms StrictEUnit.v5_polynomial_of_monic_laurent_samples
