import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.Ideal.Maps

/-!
Genuine algebraic implications used in Sections 8, 10 and 11 of the proposed
strict E-unit manuscript. These do not construct the E-function/PV rings.
-/

namespace StrictEUnit

/-- Once the logarithm extension is proved to be a polynomial ring over a
domain, a unit is a constant polynomial with a unit constant coefficient.
The transcendence/analytic-continuation premise is not proved here. -/
theorem polynomial_unit_is_constant {R : Type*} [CommRing R] [IsDomain R]
    (p : Polynomial R) (hp : IsUnit p) :
    ∃ r : R, IsUnit r ∧ Polynomial.C r = p :=
  Polynomial.isUnit_iff.mp hp

/-- The purely algebraic contradiction used by the logarithm-monodromy
argument: a polynomial with an injectively indexed infinite family of roots
must be zero. Producing that family by analytic continuation remains outside
this file. -/
theorem polynomial_eq_zero_of_infinite_root_sequence
    {K : Type*} [CommRing K] [IsDomain K]
    (p : Polynomial K) (x : ℕ → K) (hx : Function.Injective x)
    (hroot : ∀ n, p.eval (x n) = 0) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.infinite_range_of_injective hx).mono
  rintro _ ⟨n, rfl⟩
  exact hroot n

/-- A regular functional unit cannot specialize to zero under a unital ring
homomorphism into a nontrivial ring. -/
theorem specialization_of_unit_ne_zero
    {R S : Type*} [CommRing R] [CommRing S] [Nontrivial S]
    (ev : R →+* S) (v : R) (hv : IsUnit v) : ev v ≠ 0 :=
  (hv.map ev).ne_zero

/-- Abstract kernel-reduction principle for the exact numerical fiber.
`hrepresent` is reduction modulo the parameter ideal; `hlift` is the exact
relation-lifting consequence. Neither premise is automatically true of a
numerical evaluation map, and Beukers' theorem is NOT formalized here. -/
theorem kernel_eq_of_representatives
    {R S A : Type*} [CommRing R] [CommRing S]
    (ev : R →+* S) (J : Ideal R) (repr : A → R)
    (hJ : J ≤ RingHom.ker ev)
    (hrepresent : ∀ r : R, ∃ a : A, r - repr a ∈ J)
    (hlift : ∀ a : A, ev (repr a) = 0 → repr a ∈ J) :
    RingHom.ker ev = J := by
  apply le_antisymm _ hJ
  intro r hr
  obtain ⟨a, ha⟩ := hrepresent r
  have hra : ev (r - repr a) = 0 := hJ ha
  have hr0 : ev r = 0 := hr
  have hav : ev (repr a) = 0 := by
    simpa [map_sub, hr0] using hra
  have hsum := J.add_mem ha (hlift a hav)
  simpa using hsum

end StrictEUnit

#print axioms StrictEUnit.polynomial_unit_is_constant
#print axioms StrictEUnit.polynomial_eq_zero_of_infinite_root_sequence
#print axioms StrictEUnit.specialization_of_unit_ne_zero
#print axioms StrictEUnit.kernel_eq_of_representatives
