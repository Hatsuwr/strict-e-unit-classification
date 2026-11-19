import HomogeneousDehomogenization
import PolynomialDegreeReduction
import Mathlib.RingTheory.Nullstellensatz

/-! A homogeneous affine presentation with no points at infinity has a
finite-dimensional dehomogenized coordinate ring. The proof uses the actual
Nullstellensatz, homogeneous-component extraction, and degree reduction. -/
noncomputable section
open MvPolynomial
namespace StrictEUnit
variable {k ι : Type*} [Field k] [IsAlgClosed k] [Fintype ι]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem positive_coordinate_power_of_no_infinity
    (I : Ideal (MvPolynomial (Option ι) k))
    (hno : ∀ x : Option ι → k, (∀ f ∈ I, eval x f = 0) →
      x none = 0 → ∀ i, x (some i) = 0) (i : ι) :
    ∃ N : ℕ, 0 < N ∧ X (some i) ^ N ∈ I ⊔ Ideal.span {X none} := by
  classical
  let J := I ⊔ Ideal.span {X none}
  have hx : X (some i) ∈ J.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical]
    intro x hx
    have ht : x none = 0 := by
      have he := hx (X none) (show X none ∈ J from
        (show Ideal.span {X none} ≤ J from le_sup_right)
          (Ideal.subset_span (Set.mem_singleton _)))
      simpa using he
    simpa using hno x (fun f hf => hx f ((show I ≤ J from le_sup_left) hf)) ht i
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hx
  refine ⟨n+1, Nat.succ_pos _, ?_⟩
  simpa only [pow_succ] using J.mul_mem_right (X (some i)) hn

theorem finite_dehomogenized_quotient_of_no_infinity
    (I : Ideal (MvPolynomial (Option ι) k))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Option ι) k))
    (hno : ∀ x : Option ι → k, (∀ f ∈ I, eval x f = 0) →
      x none = 0 → ∀ i, x (some i) = 0) :
    Module.Finite k (MvPolynomial ι k ⧸ Ideal.map dehomogenize.toRingHom I) := by
  classical
  choose N hN hpow using positive_coordinate_power_of_no_infinity I hno
  choose q hq hrel using fun i => dehomogenize_power_relation I hI i (N i) (hN i) (hpow i)
  exact finite_quotient_of_degree_lowering _ N q hq hrel

end StrictEUnit
#print axioms StrictEUnit.positive_coordinate_power_of_no_infinity
#print axioms StrictEUnit.finite_dehomogenized_quotient_of_no_infinity
