import Mathlib.Algebra.MvPolynomial.CommRing
import AlgebraicInterfaces
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Polynomial.Div

/-! Algebraic content of exact relation lifting. Representatives are derived
from actual algebra generation; polynomial lifts imply ideal membership by
actual divisibility by z-1. Existence of the polynomial lifts is explicit. -/
noncomputable section
namespace StrictEUnit
variable {k R S ι σ : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]

/-- No algebraic independence of the generators is required. -/
theorem generated_polynomial_representative
    (F : ι → R) (c : σ → R) (J : Ideal R)
    (hc : ∀ s, ∃ a : k, c s - algebraMap k R a ∈ J)
    {r : R} (hr : r ∈ Algebra.adjoin k (Set.range F ∪ Set.range c)) :
    ∃ P : MvPolynomial ι k, r - MvPolynomial.aeval F P ∈ J := by
  have h : ∃ P : MvPolynomial ι k,
      Ideal.Quotient.mk J r = Ideal.Quotient.mk J (MvPolynomial.aeval F P) := by
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨i,rfl⟩ | ⟨s,rfl⟩
      · exact ⟨MvPolynomial.X i, by simp⟩
      · obtain ⟨a,ha⟩ := hc s
        exact ⟨MvPolynomial.C a, by simpa using
          (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ha⟩
    | algebraMap a => exact ⟨MvPolynomial.C a, by simp⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨P,hP⟩ := ihx
      obtain ⟨Q,hQ⟩ := ihy
      exact ⟨P+Q, by simp only [map_add,hP,hQ]⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨P,hP⟩ := ihx
      obtain ⟨Q,hQ⟩ := ihy
      exact ⟨P*Q, by simp only [map_mul,hP,hQ]⟩
  obtain ⟨P,hP⟩ := h
  exact ⟨P,(Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp hP⟩

/-- Substitution into Q-Q(1) proves the desired relation belongs to (z-1). -/
theorem lifted_polynomial_relation_mem
    (F : ι → R) (z : R) (J : Ideal R) (hz : z-1 ∈ J)
    (P : MvPolynomial ι k) (Q : Polynomial (MvPolynomial ι k))
    (hQ : Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom z Q = 0)
    (hP : Q.eval 1 = P) : MvPolynomial.aeval F P ∈ J := by
  have hd := Polynomial.X_sub_C_dvd_sub_C_eval (p := Q) (a := (1 : MvPolynomial ι k))
  have hd' := (Polynomial.eval₂RingHom (MvPolynomial.aeval F).toRingHom z).map_dvd hd
  have hdiv : z-1 ∣ -MvPolynomial.aeval F P := by
    simp only [map_sub, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.eval₂_C, map_one] at hd'
    change z - 1 ∣ Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom z Q -
      MvPolynomial.aeval F (Q.eval 1) at hd'
    rw [hQ,hP,zero_sub] at hd'
    exact hd'
  obtain ⟨r,hr⟩ := hdiv
  have hm : -MvPolynomial.aeval F P ∈ J := hr ▸ J.mul_mem_right r hz
  simpa using J.neg_mem hm

/-- The explicit relation-lifting statement, not an assumed kernel theorem,
now yields exactness of specialization on the generated algebra. -/
theorem kernel_eq_of_generated_polynomial_lifts
    (ev : R →ₐ[k] S) (F : ι → R) (c : σ → R) (z : R) (J : Ideal R)
    (hgen : Algebra.adjoin k (Set.range F ∪ Set.range c) = ⊤)
    (hc : ∀ s, ∃ a : k, c s - algebraMap k R a ∈ J)
    (hJ : J ≤ RingHom.ker ev.toRingHom) (hz : z-1 ∈ J)
    (hlift : ∀ P : MvPolynomial ι k, ev (MvPolynomial.aeval F P) = 0 →
      ∃ Q : Polynomial (MvPolynomial ι k),
        Polynomial.eval₂ (MvPolynomial.aeval F).toRingHom z Q = 0 ∧ Q.eval 1 = P) :
    RingHom.ker ev.toRingHom = J := by
  apply kernel_eq_of_representatives ev.toRingHom J (MvPolynomial.aeval (R := k) F) hJ
  · intro r
    apply generated_polynomial_representative F c J hc
    rw [hgen]
    trivial
  · intro P hP
    obtain ⟨Q,hQ,hQP⟩ := hlift P hP
    exact lifted_polynomial_relation_mem F z J hz P Q hQ hQP
end StrictEUnit
#print axioms StrictEUnit.generated_polynomial_representative
#print axioms StrictEUnit.lifted_polynomial_relation_mem
#print axioms StrictEUnit.kernel_eq_of_generated_polynomial_lifts
