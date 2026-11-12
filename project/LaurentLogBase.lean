import PicardIngredient
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Ideal

/-!
Concrete abstract base ring for the proposed argument: k[t,t⁻¹,ell].
The field assumption on k suffices for the domain and UFD conclusions.
This file does not identify ell with an analytic logarithm, build an analytic
embedding, or instantiate k as the algebraic numbers inside the complex field.
-/

noncomputable section

open scoped nonZeroDivisors

namespace StrictEUnit

/-- The abstract ring k[t,t⁻¹,ell], with ell the outer polynomial variable. -/
abbrev LaurentLogBase (k : Type*) [CommRing k] := Polynomial (LaurentPolynomial k)

/-- Localization preserves the principal-ideal-ring property: extend the
principal contraction of each ideal back to the localization. -/
theorem principalIdealRing_of_localization
    (A S : Type*) [CommRing A] [CommRing S] [IsPrincipalIdealRing A]
    (M : Submonoid A) [Algebra A S] [IsLocalization M S] :
    IsPrincipalIdealRing S := by
  constructor
  intro I
  rw [← IsLocalization.map_comap M S I]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap A S) inferInstance

/-- Laurent polynomials over a field are a domain because they localize k[t]
at powers of the nonzero polynomial t. -/
theorem laurentPolynomial_isDomain (k : Type*) [Field k] :
    IsDomain (LaurentPolynomial k) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors (Polynomial k)
    (M := Submonoid.powers (Polynomial.X : Polynomial k))
  intro p hp
  obtain ⟨n, rfl⟩ := hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n Polynomial.X_ne_zero)

attribute [instance] laurentPolynomial_isDomain

/-- A single-variable Laurent polynomial ring over a field is a principal
ideal ring; no PID assertion is made about the extra ell polynomial variable. -/
theorem laurentPolynomial_isPrincipalIdealRing (k : Type*) [Field k] :
    IsPrincipalIdealRing (LaurentPolynomial k) := by
  exact principalIdealRing_of_localization (Polynomial k) (LaurentPolynomial k)
    (Submonoid.powers (Polynomial.X : Polynomial k))

attribute [instance] laurentPolynomial_isPrincipalIdealRing

/-- The Laurent coefficient ring is a UFD, proved from its PID property. -/
theorem laurentPolynomial_uniqueFactorizationMonoid (k : Type*) [Field k] :
    UniqueFactorizationMonoid (LaurentPolynomial k) := by
  letI := laurentPolynomial_isDomain k
  letI := laurentPolynomial_isPrincipalIdealRing k
  infer_instance

/-- The full abstract base k[t,t⁻¹,ell] is an integral domain. -/
theorem laurentLogBase_isDomain (k : Type*) [Field k] :
    IsDomain (LaurentLogBase k) := by
  letI := laurentPolynomial_isDomain k
  infer_instance

/-- The full abstract base k[t,t⁻¹,ell] is a UFD. Unique factorization is a
conclusion, not a supplied hypothesis on this base. -/
theorem laurentLogBase_uniqueFactorizationMonoid (k : Type*) [Field k] :
    UniqueFactorizationMonoid (LaurentLogBase k) := by
  letI := laurentPolynomial_isDomain k
  letI := laurentPolynomial_uniqueFactorizationMonoid k
  infer_instance

/-- Every invertible fractional ideal of the actual abstract base ring is
principal, by the checked UFD fractional-ideal theorem. -/
theorem laurentLogBase_invertible_fractional_ideal_isPrincipal
    (k : Type*) [Field k]
    (I : FractionalIdeal (LaurentLogBase k)⁰ (FractionRing (LaurentLogBase k)))
    (hI : IsUnit I) : (I : Submodule (LaurentLogBase k)
      (FractionRing (LaurentLogBase k))).IsPrincipal := by
  letI := laurentLogBase_isDomain k
  letI := laurentLogBase_uniqueFactorizationMonoid k
  exact invertible_fractional_ideal_isPrincipal I hI

end StrictEUnit

#print axioms StrictEUnit.LaurentLogBase
#print axioms StrictEUnit.principalIdealRing_of_localization
#print axioms StrictEUnit.laurentPolynomial_isDomain
#print axioms StrictEUnit.laurentPolynomial_isPrincipalIdealRing
#print axioms StrictEUnit.laurentPolynomial_uniqueFactorizationMonoid
#print axioms StrictEUnit.laurentLogBase_isDomain
#print axioms StrictEUnit.laurentLogBase_uniqueFactorizationMonoid
#print axioms StrictEUnit.laurentLogBase_invertible_fractional_ideal_isPrincipal
