import Mathlib.RingTheory.Unramified.Basic
import Mathlib.Tactic.Ring

noncomputable section
namespace StrictEUnit

/-- Formally unramified algebras have no nonzero relative derivations. -/
theorem v5_unramified_derivation_eq_zero
    {B T M : Type*} [CommRing B] [CommRing T] [Algebra B T]
    [AddCommGroup M] [Module B M] [Module T M] [IsScalarTower B T M]
    [Algebra.FormallyUnramified B T] (d : Derivation B T M) : d = 0 := by
  haveI : Subsingleton (Derivation B T M) :=
    (KaehlerDifferential.linearMapEquivDerivation B T).toEquiv.surjective.subsingleton
  exact Subsingleton.elim _ _

/-- Two twisted derivations into the same module that agree on the base
agree everywhere on a formally unramified algebra. -/
theorem v5_unramified_twisted_derivations_unique
    {B T M : Type*} [CommRing B] [CommRing T] [Algebra B T]
    [AddCommGroup M] [Module B M] [Module T M] [IsScalarTower B T M]
    [Algebra.FormallyUnramified B T]
    (d₁ d₂ : T →+ M)
    (h₁ : ∀ a b, d₁ (a*b) = a • d₁ b + b • d₁ a)
    (h₂ : ∀ a b, d₂ (a*b) = a • d₂ b + b • d₂ a)
    (hbase : ∀ b : B, d₁ (algebraMap B T b) = d₂ (algebraMap B T b)) :
    d₁ = d₂ := by
  let l : T →ₗ[B] M :=
    { toAddHom := d₁ - d₂
      map_smul' := by
        intro b t
        change d₁ (b • t) - d₂ (b • t) = b • (d₁ t - d₂ t)
        rw [Algebra.smul_def, h₁, h₂, hbase]
        simp only [add_sub_add_right_eq_sub, ← smul_sub, IsScalarTower.algebraMap_smul] }
  let d : Derivation B T M := Derivation.mk' l (by
    intro a b
    change d₁ (a*b) - d₂ (a*b) = a • (d₁ b - d₂ b) + b • (d₁ a - d₂ a)
    rw [h₁, h₂, smul_sub, smul_sub]
    abel)
  have hd := v5_unramified_derivation_eq_zero d
  ext t
  have ht := congrArg (fun e : Derivation B T M => e t) hd
  change d₁ t - d₂ t = 0 at ht
  exact sub_eq_zero.mp ht

/-- An algebra map from a formally unramified B-algebra automatically
intertwines a scaled source derivation once this is true on B. This is the
Kummer adapter: q need not be inverted or even be a unit. -/
theorem v5_unramified_scaled_differential_map
    {k B T S : Type*} [CommRing k] [CommRing B] [CommRing T] [CommRing S]
    [Algebra k T] [Algebra k S] [Algebra B T]
    [Algebra.FormallyUnramified B T]
    (f : T →ₐ[k] S) (dT : Derivation k T T) (dS : Derivation k S S) (q : S)
    (hbase : ∀ b : B, dS (f (algebraMap B T b)) = q * f (dT (algebraMap B T b))) :
    ∀ t : T, dS (f t) = q * f (dT t) := by
  letI : Algebra T S := f.toRingHom.toAlgebra
  letI : Algebra B S := (f.toRingHom.comp (algebraMap B T)).toAlgebra
  haveI : IsScalarTower B T S := IsScalarTower.of_algebraMap_eq' rfl
  let d₁ : T →+ S := dS.toAddMonoidHom.comp f.toAddMonoidHom
  let d₂ : T →+ S := q • (f.toAddMonoidHom.comp dT.toAddMonoidHom)
  have he : d₁ = d₂ := v5_unramified_twisted_derivations_unique d₁ d₂
    (by
      intro a b
      change dS (f (a*b)) = f a * dS (f b) + f b * dS (f a)
      rw [map_mul, dS.leibniz]
      rfl)
    (by
      intro a b
      change q * f (dT (a*b)) = f a * (q * f (dT b)) + f b * (q * f (dT a))
      rw [dT.leibniz]
      simp only [smul_eq_mul, map_add, map_mul]
      ring)
    hbase
  intro t
  exact congrArg (fun d : T →+ S => d t) he

/-- The Euler derivative of t^q is q*t^q, including q=0. -/
theorem v5_euler_derivation_pow
    {k S : Type*} [CommRing k] [CommRing S] [Algebra k S]
    (d : Derivation k S S) (t : S) (ht : d t = t) (q : ℕ) :
    d (t ^ q) = (q : S) * t ^ q := by
  cases q with
  | zero => simp
  | succ n =>
    rw [d.leibniz_pow, ht]
    simp only [Nat.add_sub_cancel, smul_eq_mul, nsmul_eq_mul]
    simp only [pow_succ, mul_assoc]

/-- Compatibility on the Kummer coordinate z↦t^q. The unramified adapter
above promotes full base compatibility to the finite cover. -/
theorem v5_kummer_coordinate_euler_compatibility
    {k T S : Type*} [CommRing k] [CommRing T] [CommRing S]
    [Algebra k T] [Algebra k S]
    (f : T →ₐ[k] S) (dT : Derivation k T T) (dS : Derivation k S S)
    (z : T) (t : S) (q : ℕ) (hz : dT z = z) (ht : dS t = t)
    (hf : f z = t ^ q) : dS (f z) = (q : S) * f (dT z) := by
  rw [hz, hf]
  exact v5_euler_derivation_pow dS t ht q

end StrictEUnit
#print axioms StrictEUnit.v5_unramified_derivation_eq_zero
#print axioms StrictEUnit.v5_unramified_twisted_derivations_unique
#print axioms StrictEUnit.v5_unramified_scaled_differential_map
#print axioms StrictEUnit.v5_euler_derivation_pow
#print axioms StrictEUnit.v5_kummer_coordinate_euler_compatibility
