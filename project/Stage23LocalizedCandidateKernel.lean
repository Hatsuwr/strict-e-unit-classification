import Stage23AdjoinedInverseLocalization
import LocalizedBasePointFiber

/-! Exact kernels on actual inverse-adjoined subalgebras are transported to
the existing numerical map, rather than constructing a different evaluation. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
variable {k B L K : Type*} [Field k] [CommRing B] [Field L] [CommRing K]
    [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
    [Algebra B k] [Algebra k K]

/-- The exact base-point kernel extends to the actual inverse-adjoined ring,
for the already constructed numerical evaluation on that ring. -/
theorem stage23_subalgebra_localized_kernel
    (R S : Subalgebra B L) (hRS : R ≤ S) (d : R) (hd : d ≠ 0)
    (hS : S = Algebra.adjoin B (insert (d : L)⁻¹ (R : Set L)))
    (ν : S →ₐ[k] K)
    (hker : RingHom.ker
      (ν.comp ((Subalgebra.inclusion hRS).restrictScalars k)).toRingHom =
      Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    RingHom.ker ν.toRingHom =
      Ideal.map (algebraMap B S) (RingHom.ker (algebraMap B k)) := by
  letI : Algebra R S := (Subalgebra.inclusion hRS).toRingHom.toAlgebra
  letI : IsScalarTower B R S := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsLocalization.Away d S :=
    subalgebra_inclusion_isLocalization_away R S hRS d hd hS
  have h := localized_specialization_kernel (Submonoid.powers d)
    (ν.comp ((Subalgebra.inclusion hRS).restrictScalars k)).toRingHom ν.toRingHom
    (by rfl) _ hker
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq B R S] at h
  exact h

end StrictEUnit
