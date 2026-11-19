import V5KummerCoassoc135
import V5CanonicalOppositeUnit135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k T L R N : Type*}
  [Field k] [CommRing T] [CommRing L] [IsDomain L] [IsPrincipalIdealRing L]
  [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R] [Module.FaithfullyFlat T R]
theorem v5KummerPIDOpposite135
    (Δ : N →ₐ[k] N ⊗[k] N) (ε : N →ₐ[k] k)
    (hleft : ∀ n, v5ComponentLeftScalar ε (Δ n) = n)
    (ρ : R →ₐ[T] R ⊗[k] N) (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R N N
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (χ : Nˣ) (hχ : Δ (χ : N) = (χ : N) ⊗ₜ[k] (χ : N))
    (hε : ε (χ : N) = 1) :
    ∃ v : L ⊗[T] R, v5KummerCoaction135 ρ v = v ⊗ₜ[k] (↑χ⁻¹ : N) ∧ IsUnit v := by
  letI := v5KummerBaseChangeFaithfullyFlat135 (T := T) (L := L) (R := R)
  exact v5_pid_opposite_weight_unit_of_canonical_chart135 Δ ε hleft
    (v5KummerCoaction135 ρ) (v5KummerBaseChangeChart135 e)
    (v5KummerBaseChangeChart135_tmul e ρ he)
    (v5KummerCoaction135_coassoc ρ Δ hρ) χ hχ hε
end StrictEUnit
#print axioms StrictEUnit.v5KummerPIDOpposite135
