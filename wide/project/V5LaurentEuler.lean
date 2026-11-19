import V5DifferentialKummer
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
namespace StrictEUnit

/-- On a Laurent algebra, scaled differential compatibility is determined by
the single positive coordinate; constants and its inverse are forced. -/
theorem v5_laurent_scaled_differential_map
    {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (f : LaurentPolynomial k →ₐ[k] S)
    (dL : Derivation k (LaurentPolynomial k) (LaurentPolynomial k))
    (dS : Derivation k S S) (q : S)
    (hcoord : dS (f (LaurentPolynomial.T 1)) = q * f (dL (LaurentPolynomial.T 1))) :
    ∀ p : LaurentPolynomial k, dS (f p) = q * f (dL p) := by
  have hneg : dS (f (LaurentPolynomial.T (-1))) = q * f (dL (LaurentPolynomial.T (-1))) := by
    have hi : (LaurentPolynomial.T (-1) : LaurentPolynomial k) * LaurentPolynomial.T 1 = 1 := by
      rw [← LaurentPolynomial.T_add]; norm_num
    have hif : f (LaurentPolynomial.T (-1)) * f (LaurentPolynomial.T 1) = 1 := by
      rw [← map_mul, hi, map_one]
    rw [dS.leibniz_of_mul_eq_one hif, dL.leibniz_of_mul_eq_one hi, hcoord]
    simp only [smul_eq_mul, map_neg, map_mul, map_pow]
    ring
  have hmul : ∀ a b : LaurentPolynomial k,
      dS (f a) = q * f (dL a) → dS (f b) = q * f (dL b) →
      dS (f (a*b)) = q * f (dL (a*b)) := by
    intro a b ha hb
    rw [map_mul, dS.leibniz, dL.leibniz, ha, hb]
    simp only [smul_eq_mul, map_add, map_mul]
    ring
  intro p
  induction p using LaurentPolynomial.induction_on with
  | h_C a =>
    rw [LaurentPolynomial.C_eq_algebraMap, f.commutes, dS.map_algebraMap, dL.map_algebraMap, map_zero, mul_zero]
  | h_add ha hb => simp only [map_add, ha, hb, mul_add]
  | h_C_mul_T n a hn =>
    rw [LaurentPolynomial.T_add, ← mul_assoc]
    exact hmul _ _ hn hcoord
  | h_C_mul_T_Z n a hn =>
    rw [sub_eq_add_neg, LaurentPolynomial.T_add, ← mul_assoc]
    exact hmul _ _ hn hneg

/-- Full Laurent Euler compatibility for z↦t^q, without inverting q. -/
theorem v5_laurent_kummer_euler_compatibility
    {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (f : LaurentPolynomial k →ₐ[k] S)
    (dL : Derivation k (LaurentPolynomial k) (LaurentPolynomial k))
    (dS : Derivation k S S) (t : S) (q : ℕ)
    (hL : dL (LaurentPolynomial.T 1) = LaurentPolynomial.T 1)
    (ht : dS t = t) (hf : f (LaurentPolynomial.T 1) = t ^ q) :
    ∀ p : LaurentPolynomial k, dS (f p) = (q : S) * f (dL p) := by
  apply v5_laurent_scaled_differential_map
  exact v5_kummer_coordinate_euler_compatibility f dL dS _ t q hL ht hf

/-- Full differential Kummer descent for a formally unramified finite-cover
candidate: the only map-specific input is z↦t^q. All Laurent base elements,
including inverse powers, are discharged before unramified uniqueness. -/
theorem v5_unramified_laurent_kummer_differential_map
    {k T S : Type*} [CommRing k] [CommRing T] [CommRing S]
    [Algebra k T] [Algebra k S] [Algebra (LaurentPolynomial k) T]
    [IsScalarTower k (LaurentPolynomial k) T]
    [Algebra.FormallyUnramified (LaurentPolynomial k) T]
    (f : T →ₐ[k] S)
    (dL : Derivation k (LaurentPolynomial k) (LaurentPolynomial k))
    (dT : Derivation k T T) (dS : Derivation k S S)
    (hT : ∀ p : LaurentPolynomial k,
      dT (algebraMap (LaurentPolynomial k) T p) =
        algebraMap (LaurentPolynomial k) T (dL p))
    (t : S) (q : ℕ)
    (hL : dL (LaurentPolynomial.T 1) = LaurentPolynomial.T 1)
    (ht : dS t = t)
    (hf : f (algebraMap (LaurentPolynomial k) T (LaurentPolynomial.T 1)) = t ^ q) :
    ∀ x : T, dS (f x) = (q : S) * f (dT x) := by
  apply v5_unramified_scaled_differential_map (B := LaurentPolynomial k) f dT dS
  intro p
  rw [hT]
  exact v5_laurent_kummer_euler_compatibility
    (f.comp (IsScalarTower.toAlgHom k (LaurentPolynomial k) T)) dL dS t q hL ht hf p

end StrictEUnit
#print axioms StrictEUnit.v5_laurent_scaled_differential_map
#print axioms StrictEUnit.v5_laurent_kummer_euler_compatibility
#print axioms StrictEUnit.v5_unramified_laurent_kummer_differential_map
