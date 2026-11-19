import Mathlib.Algebra.TrivSqZeroExt
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
open scoped TensorProduct
attribute [-instance] TensorProduct.leftModule
attribute [-instance] TrivSqZeroExt.algebra'
attribute [-instance] TrivSqZeroExt.smul
attribute [local instance 2000] Algebra.toModule
namespace StrictEUnit

/-- A derivation gives a ring map into square-zero jets after any ring map. -/
def v5DerivativeJet {k S C : Type*} [CommRing k] [CommRing S] [CommRing C]
    [Algebra k S] (i : S →+* C) (d : Derivation k S S) : S →+* TrivSqZeroExt C C where
  toFun s := ⟨i s, i (d s)⟩
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' s t := by apply TrivSqZeroExt.ext <;> simp
  map_mul' s t := by
    apply TrivSqZeroExt.ext
    · exact map_mul i s t
    · simp [d.leibniz, smul_eq_mul, mul_comm]

/-- Balanced square-zero jet map: the scalar algebra on the target is twisted
by the common derivative on B. No separate B-linearity of either derivative
is assumed. -/
def v5BalancedTensorJet {k B S D : Type*} [CommRing k] [CommRing B]
    [CommRing S] [CommRing D] [Algebra B S] [Algebra B D]
    [Algebra k S] [Algebra k D]
    (dS : Derivation k S S) (dD : Derivation k D D)
    (hbase : ∀ b : B,
      (dS (algebraMap B S b)) ⊗ₜ[B] (1 : D) =
        (1 : S) ⊗ₜ[B] dD (algebraMap B D b)) := by
  let i : S →+* S ⊗[B] D := Algebra.TensorProduct.includeLeftRingHom
  let j : D →+* S ⊗[B] D := Algebra.TensorProduct.includeRight.toRingHom
  let F := v5DerivativeJet i dS
  let G := v5DerivativeJet j dD
  letI twisted : Algebra B (TrivSqZeroExt (S ⊗[B] D) (S ⊗[B] D)) :=
    (F.comp (algebraMap B S)).toAlgebra
  let F' : S →ₐ[B] TrivSqZeroExt (S ⊗[B] D) (S ⊗[B] D) :=
    { F with commutes' := fun _ => rfl }
  let G' : D →ₐ[B] TrivSqZeroExt (S ⊗[B] D) (S ⊗[B] D) :=
    { G with
      commutes' := by
        intro b
        apply TrivSqZeroExt.ext
        · change (1 : S) ⊗ₜ[B] algebraMap B D b = algebraMap B S b ⊗ₜ[B] (1 : D)
          simp [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
        · exact (hbase b).symm }
  exact (@Algebra.TensorProduct.lift B B S D (TrivSqZeroExt (S ⊗[B] D) (S ⊗[B] D))
    _ _ _ _ _ _ _ _ _ _ twisted twisted ⟨fun a b c => by
      change (F (algebraMap B S (a*b))) * c = F (algebraMap B S a) * (F (algebraMap B S b) * c)
      rw [map_mul, map_mul, mul_assoc]⟩ F' G' (fun _ _ => Commute.all _ _)).toRingHom

section
variable {k B S D : Type*} [CommRing k] [CommRing B]
    [CommRing S] [CommRing D] [Algebra B S] [Algebra B D]
    [Algebra k S] [Algebra k D]
    (dS : Derivation k S S) (dD : Derivation k D D)
    (hbase : ∀ b : B, dS (algebraMap B S b) ⊗ₜ[B] (1 : D) =
      (1 : S) ⊗ₜ[B] dD (algebraMap B D b))

def v5BalancedTensorEuler : S ⊗[B] D →+ S ⊗[B] D where
  toFun x := (v5BalancedTensorJet dS dD hbase x).snd
  map_zero' := by simp
  map_add' x y := by simp

theorem v5BalancedTensorJet_fst_tmul (s : S) (d : D) :
    (v5BalancedTensorJet dS dD hbase (s ⊗ₜ[B] d)).fst = s ⊗ₜ[B] d := by
  simp [v5BalancedTensorJet, Algebra.TensorProduct.lift_tmul, v5DerivativeJet,
    Algebra.TensorProduct.tmul_mul_tmul]

theorem v5BalancedTensorEuler_tmul (s : S) (d : D) :
    v5BalancedTensorEuler dS dD hbase (s ⊗ₜ[B] d) = dS s ⊗ₜ[B] d + s ⊗ₜ[B] dD d := by
  change (v5BalancedTensorJet dS dD hbase (s ⊗ₜ[B] d)).snd = _
  simp only [v5BalancedTensorJet, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.lift_tmul]
  change (s ⊗ₜ[B] (1 : D)) * ((1 : S) ⊗ₜ[B] dD d) +
    (dS s ⊗ₜ[B] (1 : D)) * ((1 : S) ⊗ₜ[B] d) = _
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  exact add_comm _ _

theorem v5BalancedTensorJet_fst (x : S ⊗[B] D) :
    (v5BalancedTensorJet dS dD hbase x).fst = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s d => exact v5BalancedTensorJet_fst_tmul dS dD hbase s d
  | add x y hx hy => simp [hx,hy]

theorem v5BalancedTensorEuler_leibniz (x y : S ⊗[B] D) :
    v5BalancedTensorEuler dS dD hbase (x*y) =
      x * v5BalancedTensorEuler dS dD hbase y + y * v5BalancedTensorEuler dS dD hbase x := by
  change (v5BalancedTensorJet dS dD hbase (x*y)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, v5BalancedTensorJet_fst, v5BalancedTensorJet_fst]
  simp only [smul_eq_mul, MulOpposite.smul_eq_mul_unop]
  change x * _ + _ * y = x * _ + y * _
  rw [mul_comm _ y]
  rfl
end

end StrictEUnit
#print axioms StrictEUnit.v5DerivativeJet
#print axioms StrictEUnit.v5BalancedTensorJet

#print axioms StrictEUnit.v5BalancedTensorEuler_tmul
#print axioms StrictEUnit.v5BalancedTensorEuler_leibniz
