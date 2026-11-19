import V5MixedRelativeCoaction
import CandidateCounit

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R S H : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing S] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S] [Algebra k H]

/-- Contract a constant tensor factor by its counit. -/
def v5TensorCounitEval (ε : H →ₐ[k] k) : R ⊗[k] H →ₐ[k] R :=
  Algebra.TensorProduct.lift (AlgHom.id k R)
    ((Algebra.ofId k R).comp ε) (fun _ _ => Commute.all _ _)

@[simp] theorem v5TensorCounitEval_tmul (ε : H →ₐ[k] k) (r : R) (h : H) :
    v5TensorCounitEval ε (r ⊗ₜ[k] h) = ε h • r := by
  change r * algebraMap k R (ε h) = ε h • r
  rw [Algebra.smul_def, mul_comm]

/-- Contracting the constant factor commutes with mixed base change. -/
theorem v5MixedCoactionShuffle_counit (ε : H →ₐ[k] k) (s : S) (z : R ⊗[k] H) :
    v5TensorCounitEval ε (v5MixedCoactionShuffle (s ⊗ₜ[B] z)) =
      v5TensorCounitEval ε z ⊗ₜ[B] s := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [tmul_zero, map_zero, zero_tmul]
  | add x y hx hy => simp only [tmul_add, map_add, add_tmul, hx, hy]
  | tmul r h =>
    simp only [v5MixedCoactionShuffle_tmul, v5TensorCounitEval_tmul, smul_tmul']

/-- Counitality survives base change to any mixed solution algebra. -/
theorem v5MixedRelativeCoaction_counit (ρ : R →ₐ[B] R ⊗[k] H)
    (ε : H →ₐ[k] k) (hc : ∀ r, v5TensorCounitEval ε (ρ r) = r)
    (x : R ⊗[B] S) :
    v5TensorCounitEval ε (v5MixedRelativeCoaction ρ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    rw [v5MixedRelativeCoaction_tmul, v5MixedCoactionShuffle_counit, hc]

end StrictEUnit
#print axioms StrictEUnit.v5TensorCounitEval
#print axioms StrictEUnit.v5TensorCounitEval_tmul
#print axioms StrictEUnit.v5MixedCoactionShuffle_counit
#print axioms StrictEUnit.v5MixedRelativeCoaction_counit
