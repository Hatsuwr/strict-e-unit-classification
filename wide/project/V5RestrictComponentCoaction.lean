import V5DomainCoactionUnit

/-! Restriction along a supplied coordinate algebra map H → N preserving
counit and comultiplication. This does not construct the identity component,
its ideal, or a Kummer cover. No surjectivity is needed for these laws. -/
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k C H N : Type*} [Field k] [CommRing C] [CommRing H] [CommRing N]
  [Algebra k C] [Algebra k H] [Algebra k N]

def v5RestrictComponentCoaction (δ : C →ₐ[k] C ⊗[k] H) (q : H →ₐ[k] N) :
    C →ₐ[k] C ⊗[k] N :=
  (Algebra.TensorProduct.map (AlgHom.id k C) q).comp δ

theorem v5RestrictComponentCoaction_apply (δ : C →ₐ[k] C ⊗[k] H)
    (q : H →ₐ[k] N) (c : C) :
    v5RestrictComponentCoaction δ q c =
      TensorProduct.map (LinearMap.id) q.toLinearMap (δ c) := rfl

theorem v5RestrictComponentCoaction_counit
    (δ : C →ₐ[k] C ⊗[k] H) (q : H →ₐ[k] N)
    (εH : H →ₐ[k] k) (εN : N →ₐ[k] k)
    (hq : ∀ h, εN (q h) = εH h)
    (hcounit : ∀ c, TensorProduct.rid k C (εH.toLinearMap.lTensor C (δ c)) = c)
    (c : C) :
    TensorProduct.rid k C
      (εN.toLinearMap.lTensor C (v5RestrictComponentCoaction δ q c)) = c := by
  have he (x : C ⊗[k] H) :
      TensorProduct.rid k C (εN.toLinearMap.lTensor C
        (TensorProduct.map (LinearMap.id) q.toLinearMap x)) =
      TensorProduct.rid k C (εH.toLinearMap.lTensor C x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c h =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, AlgHom.toLinearMap_apply, hq]
  rw [v5RestrictComponentCoaction_apply, he, hcounit]

theorem v5RestrictComponentCoaction_coassoc
    (δ : C →ₐ[k] C ⊗[k] H) (q : H →ₐ[k] N)
    (ΔH : H →ₐ[k] H ⊗[k] H) (ΔN : N →ₐ[k] N ⊗[k] N)
    (hq : ∀ h, ΔN (q h) = TensorProduct.map q.toLinearMap q.toLinearMap (ΔH h))
    (hcoassoc : ∀ c, TensorProduct.assoc k C H H
      (δ.toLinearMap.rTensor H (δ c)) = ΔH.toLinearMap.lTensor C (δ c))
    (c : C) :
    TensorProduct.assoc k C N N
      ((v5RestrictComponentCoaction δ q).toLinearMap.rTensor N
        (v5RestrictComponentCoaction δ q c)) =
      ΔN.toLinearMap.lTensor C (v5RestrictComponentCoaction δ q c) := by
  have hl (x : C ⊗[k] H) :
      TensorProduct.map (TensorProduct.map (LinearMap.id) q.toLinearMap) q.toLinearMap
        (δ.toLinearMap.rTensor H x) =
      (v5RestrictComponentCoaction δ q).toLinearMap.rTensor N
        (TensorProduct.map (LinearMap.id) q.toLinearMap x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c h => rfl
  have hr (x : C ⊗[k] H) :
      TensorProduct.map (LinearMap.id)
        (TensorProduct.map q.toLinearMap q.toLinearMap)
        (ΔH.toLinearMap.lTensor C x) =
      ΔN.toLinearMap.lTensor C (TensorProduct.map (LinearMap.id) q.toLinearMap x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c h =>
      simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, LinearMap.id_apply,
        AlgHom.toLinearMap_apply, hq]
  have he := congrArg
    (TensorProduct.map (LinearMap.id : C →ₗ[k] C)
      (TensorProduct.map q.toLinearMap q.toLinearMap)) (hcoassoc c)
  rw [TensorProduct.map_map_assoc, hl, hr] at he
  exact he

/-- Once the restricted coordinate algebra and acted-on algebra are domains,
the restricted coaction gives a genuine normalized unit character. -/
theorem v5RestrictComponentCoaction_unit_character
    [IsAlgClosed k] [IsDomain C] [IsDomain N]
    (δ : C →ₐ[k] C ⊗[k] H) (q : H →ₐ[k] N)
    (εH : H →ₐ[k] k) (εN : N →ₐ[k] k)
    (ΔH : H →ₐ[k] H ⊗[k] H) (ΔN : N →ₐ[k] N ⊗[k] N)
    (hqε : ∀ h, εN (q h) = εH h)
    (hqΔ : ∀ h, ΔN (q h) = TensorProduct.map q.toLinearMap q.toLinearMap (ΔH h))
    (hcounit : ∀ c, TensorProduct.rid k C (εH.toLinearMap.lTensor C (δ c)) = c)
    (hcoassoc : ∀ c, TensorProduct.assoc k C H H
      (δ.toLinearMap.rTensor H (δ c)) = ΔH.toLinearMap.lTensor C (δ c))
    (u : Cˣ) :
    ∃ χ : Nˣ, v5RestrictComponentCoaction δ q (u : C) = (u : C) ⊗ₜ[k] (χ : N) ∧
      εN (χ : N) = 1 ∧ ΔN (χ : N) = (χ : N) ⊗ₜ[k] (χ : N) :=
  v5_domainCoaction_unit_character (v5RestrictComponentCoaction δ q) εN ΔN
    (v5RestrictComponentCoaction_counit δ q εH εN hqε hcounit)
    (v5RestrictComponentCoaction_coassoc δ q ΔH ΔN hqΔ hcoassoc) u

end StrictEUnit
#print axioms StrictEUnit.v5RestrictComponentCoaction_counit
#print axioms StrictEUnit.v5RestrictComponentCoaction_coassoc
#print axioms StrictEUnit.v5RestrictComponentCoaction_unit_character
