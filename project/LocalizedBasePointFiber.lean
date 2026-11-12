import LocalizedRelationFiber
import AlgebraicFiberQuotient

/-! Actual localization and whole-fiber embedding from an exact pre-localization
kernel. Exactness itself is supplied by the polynomial-relation theorem. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B R T L : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing T] [CommRing L] [Algebra k B] [Algebra B k] [IsScalarTower k B k]
  [Algebra B R] [Algebra R T] [Algebra B T] [IsScalarTower B R T]

omit [Algebra k B] [IsScalarTower k B k] in
theorem away_basePoint_exact_kernel (d : R) [IsLocalization.Away d T]
    (ev : R →+* L) (hd : IsUnit (ev d))
    (hker : RingHom.ker ev = Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    RingHom.ker (IsLocalization.Away.lift (S:=T) d hd) =
      Ideal.map (algebraMap B T) (RingHom.ker (algebraMap B k)) := by
  rw [away_specialization_kernel (T:=T) d ev hd _ hker, Ideal.map_map,
    IsScalarTower.algebraMap_eq B R T]

/-- The actual localized whole-fiber map into the evaluation target. -/
def away_basePoint_fiberEvaluation (d : R) [IsLocalization.Away d T]
    (ev : R →+* L) (hd : IsUnit (ev d))
    (hker : RingHom.ker ev = Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    (k ⊗[B] T) →+* L :=
  algebraicFiberEvaluationFromQuotient
    (Ideal.Quotient.lift _ (IsLocalization.Away.lift (S:=T) d hd)
      (fun t ht => show t ∈ RingHom.ker (IsLocalization.Away.lift (S:=T) d hd) from
        (away_basePoint_exact_kernel (T:=T) d ev hd hker).symm ▸ ht))

theorem away_basePoint_fiberEvaluation_injective (d : R) [IsLocalization.Away d T]
    (ev : R →+* L) (hd : IsUnit (ev d))
    (hker : RingHom.ker ev = Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    Function.Injective (away_basePoint_fiberEvaluation (T:=T) d ev hd hker) := by
  apply algebraicFiberEvaluationFromQuotient_injective
  apply RingHom.lift_injective_of_ker_le_ideal
  exact le_of_eq (away_basePoint_exact_kernel (T:=T) d ev hd hker)

theorem away_basePoint_fiber_isDomain [IsDomain L] (d : R) [IsLocalization.Away d T]
    (ev : R →+* L) (hd : IsUnit (ev d))
    (hker : RingHom.ker ev = Ideal.map (algebraMap B R) (RingHom.ker (algebraMap B k))) :
    IsDomain (k ⊗[B] T) :=
  Function.Injective.isDomain _ (away_basePoint_fiberEvaluation_injective (T:=T) d ev hd hker)
end StrictEUnit
#print axioms StrictEUnit.away_basePoint_exact_kernel
#print axioms StrictEUnit.away_basePoint_fiberEvaluation
#print axioms StrictEUnit.away_basePoint_fiberEvaluation_injective
#print axioms StrictEUnit.away_basePoint_fiber_isDomain
