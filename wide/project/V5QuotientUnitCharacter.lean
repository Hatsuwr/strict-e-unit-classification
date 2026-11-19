import V5RestrictComponentCoaction
import V5ComponentCoproduct
import V5HorizontalCounit

open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 40000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k C H : Type*} [Field k] [CommRing C] [CommRing H]
  [Algebra k C] [Algebra k H]

/-- A compact statement of the actual quotient-character conclusion. The
quotient map, restricted action and quotient counit are canonical. -/
def V5QuotientUnitCharacter
    (δ : C →ₐ[k] C ⊗[k] H) (I : Ideal H) (ε : H →ₐ[k] k)
    (hI : I ≤ RingHom.ker ε.toRingHom)
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I)) : Prop :=
  ∀ u : Cˣ, ∃ χ : (H ⧸ I)ˣ,
    v5RestrictComponentCoaction δ (Ideal.Quotient.mkₐ k I) (u : C) =
      (u : C) ⊗ₜ[k] (χ : H ⧸ I) ∧
    v5ComponentCounit I ε hI (χ : H ⧸ I) = 1 ∧
    ΔI (χ : H ⧸ I) = (χ : H ⧸ I) ⊗ₜ[k] (χ : H ⧸ I)

theorem v5QuotientUnitCharacter_of_laws [IsAlgClosed k] [IsDomain C]
    (δ : C →ₐ[k] C ⊗[k] H) (I : Ideal H) [I.IsPrime]
    (ε : H →ₐ[k] k) (hI : I ≤ RingHom.ker ε.toRingHom)
    (Δ : H →ₐ[k] H ⊗[k] H)
    (ΔI : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (hΔI : ∀ h, ΔI (Ideal.Quotient.mkₐ k I h) =
      TensorProduct.map (Ideal.Quotient.mkₐ k I).toLinearMap
        (Ideal.Quotient.mkₐ k I).toLinearMap (Δ h))
    (hc : ∀ c, v5_horizontalCounit ε (δ c) = c)
    (ha : ∀ c, Algebra.TensorProduct.assoc k C H H
      (Algebra.TensorProduct.map δ (AlgHom.id k H) (δ c)) =
      Algebra.TensorProduct.map (AlgHom.id k C) Δ (δ c)) :
    V5QuotientUnitCharacter δ I ε hI ΔI := by
  have he (x : C ⊗[k] H) : v5_horizontalCounit ε x =
      TensorProduct.rid k C (ε.toLinearMap.lTensor C x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [v5_horizontalCounit]
  intro u
  exact v5RestrictComponentCoaction_unit_character δ (Ideal.Quotient.mkₐ k I)
    ε (v5ComponentCounit I ε hI) Δ ΔI (v5ComponentCounit_mk I ε hI) hΔI
    (fun c => (he _).symm.trans (hc c)) ha u

end StrictEUnit
#print axioms StrictEUnit.v5QuotientUnitCharacter_of_laws
