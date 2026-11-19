import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic

open scoped TensorProduct
open TensorProduct
noncomputable section
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 40000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k H : Type*} [Field k] [CommRing H] [Algebra k H]

/-- The scalar-valued pairing obtained by applying a character in both legs. -/
def v5CounitPairing (ε : H →ₐ[k] k) : H ⊗[k] H →ₐ[k] k :=
  Algebra.TensorProduct.lift ε ε (fun _ _ => Commute.all _ _)

@[simp] theorem v5CounitPairing_tmul (ε : H →ₐ[k] k) (x y : H) :
    v5CounitPairing ε (x ⊗ₜ[k] y) = ε x * ε y := rfl

/-- A usual right counit law implies the scalar-valued double-counit law. -/
theorem v5CounitPairing_of_right_counit (ε : H →ₐ[k] k)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hc : ∀ x, TensorProduct.rid k H (ε.toLinearMap.lTensor H (Δ x)) = x)
    (x : H) : v5CounitPairing ε (Δ x) = ε x := by
  have hp (z : H ⊗[k] H) : v5CounitPairing ε z =
      ε (TensorProduct.rid k H (ε.toLinearMap.lTensor H z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [v5CounitPairing_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        AlgHom.toLinearMap_apply, map_smul, smul_eq_mul]
      exact mul_comm _ _
  rw [hp, hc]

/-- A character descends through every ideal contained in its kernel. -/
def v5ComponentCounit (I : Ideal H) (ε : H →ₐ[k] k)
    (hI : I ≤ RingHom.ker ε.toRingHom) : H ⧸ I →ₐ[k] k :=
  Ideal.Quotient.liftₐ I ε (fun _ hx => hI hx)

@[simp] theorem v5ComponentCounit_mk (I : Ideal H) (ε : H →ₐ[k] k)
    (hI : I ≤ RingHom.ker ε.toRingHom) (x : H) :
    v5ComponentCounit I ε hI (Ideal.Quotient.mkₐ k I x) = ε x := rfl

/-- Apply a proposed coproduct and quotient both tensor factors. -/
def v5ComponentCoproductPre (I : Ideal H) (Δ : H →ₐ[k] H ⊗[k] H) :
    H →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)).comp Δ

/-- Pairing the two quotient counits recovers the original scalar character. -/
theorem v5ComponentCoproductPre_counit (I : Ideal H) (ε : H →ₐ[k] k)
    (hI : I ≤ RingHom.ker ε.toRingHom) (Δ : H →ₐ[k] H ⊗[k] H)
    (hc : ∀ x, v5CounitPairing ε (Δ x) = ε x) (x : H) :
    v5CounitPairing (v5ComponentCounit I ε hI) (v5ComponentCoproductPre I Δ x) = ε x := by
  have he (z : H ⊗[k] H) :
      v5CounitPairing (v5ComponentCounit I ε hI)
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I) z) =
      v5CounitPairing ε z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp only [Algebra.TensorProduct.map_tmul, v5CounitPairing_tmul,
        v5ComponentCounit_mk]
  exact (he (Δ x)).trans (hc x)

/-- A domain-valued morphism lying over the counit must kill the unique minimal
prime under that counit. No coproduct-stability premise is assumed. -/
theorem v5UniqueMinimalPrime_le_kernel {D : Type*} [CommRing D] [IsDomain D]
    [Algebra k D] (I : Ideal H) (ε : H →ₐ[k] k)
    (hu : ∀ p ∈ minimalPrimes H, p ≤ RingHom.ker ε.toRingHom → p = I)
    (f : H →ₐ[k] D) (hker : RingHom.ker f.toRingHom ≤ RingHom.ker ε.toRingHom) :
    I ≤ RingHom.ker f.toRingHom := by
  letI : (RingHom.ker f.toRingHom).IsPrime := RingHom.ker_isPrime f.toRingHom
  obtain ⟨p, hp, hpf⟩ := Ideal.exists_minimalPrimes_le
    (I := (⊥ : Ideal H)) (J := RingHom.ker f.toRingHom) bot_le
  rw [← hu p hp (hpf.trans hker)]
  exact hpf

/-- Domain of the quotient tensor square and uniqueness at the identity force
stability of the component ideal under the coproduct. -/
theorem v5ComponentCoproductPre_kills (I : Ideal H)
    [IsDomain ((H ⧸ I) ⊗[k] (H ⧸ I))]
    (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (hu : ∀ p ∈ minimalPrimes H, p ≤ RingHom.ker ε.toRingHom → p = I)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hc : ∀ x, v5CounitPairing ε (Δ x) = ε x) :
    I ≤ RingHom.ker (v5ComponentCoproductPre I Δ).toRingHom := by
  apply v5UniqueMinimalPrime_le_kernel I ε hu (v5ComponentCoproductPre I Δ)
  intro x hx
  change ε x = 0
  rw [← v5ComponentCoproductPre_counit I ε hI Δ hc x]
  rw [show v5ComponentCoproductPre I Δ x = 0 from hx, map_zero]

/-- The identity-component coproduct, constructed rather than postulated. -/
def v5ComponentCoproduct (I : Ideal H)
    [IsDomain ((H ⧸ I) ⊗[k] (H ⧸ I))]
    (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (hu : ∀ p ∈ minimalPrimes H, p ≤ RingHom.ker ε.toRingHom → p = I)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hc : ∀ x, v5CounitPairing ε (Δ x) = ε x) :
    H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I (v5ComponentCoproductPre I Δ)
    (fun _ hx => v5ComponentCoproductPre_kills I ε hI hu Δ hc hx)

@[simp] theorem v5ComponentCoproduct_mk (I : Ideal H)
    [IsDomain ((H ⧸ I) ⊗[k] (H ⧸ I))]
    (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (hu : ∀ p ∈ minimalPrimes H, p ≤ RingHom.ker ε.toRingHom → p = I)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (hc : ∀ x, v5CounitPairing ε (Δ x) = ε x) (x : H) :
    v5ComponentCoproduct I ε hI hu Δ hc (Ideal.Quotient.mkₐ k I x) =
      TensorProduct.map (Ideal.Quotient.mkₐ k I).toLinearMap
        (Ideal.Quotient.mkₐ k I).toLinearMap (Δ x) := rfl

end StrictEUnit
#print axioms StrictEUnit.v5CounitPairing_of_right_counit
#print axioms StrictEUnit.v5ComponentCounit
#print axioms StrictEUnit.v5ComponentCounit_mk
#print axioms StrictEUnit.v5ComponentCoproductPre_counit
#print axioms StrictEUnit.v5UniqueMinimalPrime_le_kernel
#print axioms StrictEUnit.v5ComponentCoproductPre_kills
#print axioms StrictEUnit.v5ComponentCoproduct
#print axioms StrictEUnit.v5ComponentCoproduct_mk
