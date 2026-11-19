import V5KummerCoassoc135
import V5MixedRelativeCoaction
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommAmbient136 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k B T L R W N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [CommRing L] [CommRing R]
  [CommRing W] [CommRing N]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k N]
  [Algebra B T] [Algebra B L] [Algebra B R] [Algebra B W]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
  [IsScalarTower B T L] [IsScalarTower B T R]

/-- Original own factor included in the Kummer mixed ambient. -/
def v5KummerAmbientOwnMapB136 :
    R →ₐ[B] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) :=
  ((Algebra.TensorProduct.includeLeft : (L ⊗[T] R) →ₐ[L]
    (L ⊗[T] R) ⊗[L] (L ⊗[B] W)).restrictScalars B).comp
      ((Algebra.TensorProduct.includeRight : R →ₐ[T] L ⊗[T] R).restrictScalars B)

/-- Original solution factor included in the Kummer mixed ambient. -/
def v5KummerAmbientCoeffMapB136 :
    W →ₐ[B] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) :=
  ((Algebra.TensorProduct.includeRight : (L ⊗[B] W) →ₐ[L]
    (L ⊗[T] R) ⊗[L] (L ⊗[B] W)).restrictScalars B).comp
      (Algebra.TensorProduct.includeRight : W →ₐ[B] L ⊗[B] W)

/-- The original mixed ambient maps honestly into its Kummer scalar extension. -/
def v5KummerAmbientMapB136 :
    R ⊗[B] W →ₐ[B] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) :=
  Algebra.TensorProduct.lift v5KummerAmbientOwnMapB136 v5KummerAmbientCoeffMapB136
    (fun _ _ => Commute.all _ _)

def v5KummerAmbientMap136 :
    R ⊗[B] W →ₐ[k] (L ⊗[T] R) ⊗[L] (L ⊗[B] W) :=
  (v5KummerAmbientMapB136 (B := B) (T := T) (L := L) (R := R) (W := W)).restrictScalars k

@[simp] theorem v5KummerAmbientMap136_tmul (r : R) (w : W) :
    v5KummerAmbientMap136 (k := k) (T := T) (L := L) (r ⊗ₜ[B] w) =
      ((1 : L) ⊗ₜ[T] r) ⊗ₜ[L] ((1 : L) ⊗ₜ[B] w) := by
  change (((1 : L) ⊗ₜ[T] r) ⊗ₜ[L] (1 : L ⊗[B] W)) *
    ((1 : L ⊗[T] R) ⊗ₜ[L] ((1 : L) ⊗ₜ[B] w)) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end StrictEUnit
#print axioms StrictEUnit.v5KummerAmbientMap136
#print axioms StrictEUnit.v5KummerAmbientMap136_tmul
