import V5OwnTorsorSquare
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R] [Algebra k H]
def v5QuotientOwnTargetChart126 (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (I : Ideal H) :=
  v5OwnTorsorTargetChartR (N := H ⧸ I) e.symm
end StrictEUnit
#print axioms StrictEUnit.v5QuotientOwnTargetChart126
