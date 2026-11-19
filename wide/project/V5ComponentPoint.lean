import AlgebraicPointAvoidance
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {k R : Type*} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.FiniteType k R]

/-- Finite incomparable components admit an element supported away from all
but the selected component. No reducedness or smoothness is assumed. -/
theorem v5_component_separator (P : Ideal R) [P.IsPrime]
    (s : Finset (Ideal R)) (hsep : ∀ Q ∈ s, ¬ Q ≤ P) :
    ∃ a : R, a ∉ P ∧ ∀ Q ∈ s, a ∈ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by intro h; exact (Ideal.IsPrime.ne_top (inferInstance : P.IsPrime)) (Ideal.eq_top_of_isUnit_mem P h isUnit_one), by simp⟩
  | @insert Q s hQs ih =>
    obtain ⟨a, haP, ha⟩ := ih (fun J hJ => hsep J (Finset.mem_insert_of_mem hJ))
    obtain ⟨b, hbQ, hbP⟩ := Set.not_subset.mp (hsep Q (Finset.mem_insert_self Q s))
    refine ⟨a * b, ?_, ?_⟩
    · intro hab
      exact ((Ideal.IsPrime.mem_or_mem inferInstance hab).elim haP hbP)
    · intro J hJ
      rcases Finset.mem_insert.mp hJ with rfl | hJ
      · exact J.mul_mem_left a hbQ
      · exact J.mul_mem_right b (ha J hJ)

/-- A rational point of the selected component can avoid finitely many
other incomparable components. The point itself is constructed by the
weak Nullstellensatz on R/P, not assumed. -/
theorem v5_component_separating_point (P : Ideal R) [P.IsPrime]
    (s : Finset (Ideal R)) (hsep : ∀ Q ∈ s, ¬ Q ≤ P) :
    ∃ p : R →ₐ[k] k, P ≤ RingHom.ker p.toRingHom ∧
      ∀ Q ∈ s, ¬ Q ≤ RingHom.ker p.toRingHom := by
  obtain ⟨a, haP, ha⟩ := v5_component_separator P s hsep
  have haneq : (Ideal.Quotient.mk P a : R ⧸ P) ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using haP
  obtain ⟨p, hp⟩ := exists_algebraic_point_avoiding (k := k)
    (Ideal.Quotient.mk P a) haneq
  refine ⟨p.comp (Ideal.Quotient.mkₐ k P), ?_, ?_⟩
  · intro x hx
    change p (Ideal.Quotient.mk P x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro Q hQ hle
    exact hp (hle (ha Q hQ))

/-- Every minimal component of a finite-type algebra with finitely many
minimal primes has a k-point on that component and on no other one. -/
theorem v5_minimal_component_unique_point
    (hfinite : (minimalPrimes R).Finite)
    (P : Ideal R) (hP : P ∈ minimalPrimes R) :
    ∃ p : R →ₐ[k] k, P ≤ RingHom.ker p.toRingHom ∧
      ∀ Q ∈ minimalPrimes R, Q ≤ RingHom.ker p.toRingHom → Q = P := by
  classical
  letI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
  let s := hfinite.toFinset.erase P
  have hsep : ∀ Q ∈ s, ¬ Q ≤ P := by
    intro Q hQ hle
    have hQP := Finset.mem_erase.mp hQ
    have hQmin : Q ∈ minimalPrimes R := hfinite.mem_toFinset.mp hQP.2
    exact hQP.1 (le_antisymm hle (hP.2 hQmin.1 hle))
  obtain ⟨p, hp, hpother⟩ := v5_component_separating_point (k := k) P s hsep
  refine ⟨p, hp, ?_⟩
  intro Q hQ hQp
  by_contra hne
  exact hpother Q (Finset.mem_erase.mpr ⟨hne, hfinite.mem_toFinset.mpr hQ⟩) hQp
end StrictEUnit
#print axioms StrictEUnit.v5_component_separator
#print axioms StrictEUnit.v5_component_separating_point
#print axioms StrictEUnit.v5_minimal_component_unique_point
