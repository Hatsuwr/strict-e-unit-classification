import FormalBaseChangedScalarUnitLift
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
-- Freeze the standard projection paths while the carrier is abstract.
def canonicalFieldCommRing (k : Type*) [Field k] : CommRing k := inferInstance
def canonicalFieldCommSemiring (k : Type*) [Field k] : CommSemiring k := inferInstance
def canonicalFieldSemiring (k : Type*) [Field k] : Semiring k := inferInstance
def canonicalFieldAddCommMonoid (k : Type*) [Field k] : AddCommMonoid k := inferInstance
def canonicalFieldMonoid (k : Type*) [Field k] : Monoid k := inferInstance
def canonicalRingSemiring (R : Type*) [CommRing R] : Semiring R := inferInstance
def canonicalRingAddCommMonoid (R : Type*) [CommRing R] : AddCommMonoid R := inferInstance
def canonicalRingMonoid (R : Type*) [CommRing R] : Monoid R := inferInstance
end StrictEUnit
