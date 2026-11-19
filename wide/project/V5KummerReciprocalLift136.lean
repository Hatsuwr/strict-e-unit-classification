import V5KummerAmbientMark136
import V5KummerAmbientCoaction136
import V5KummerPIDOpposite135
import V5MixedMarkedChosen136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B T L R W N C : Type*}
  [Field k] [CommRing B] [CommRing T] [CommRing L] [IsDomain L] [IsPrincipalIdealRing L]
  [CommRing R] [CommRing W] [CommRing N] [CommRing C]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W]
  [Algebra k N] [Algebra k C]
  [Algebra B T] [Algebra T L] [Algebra T R] [Algebra B L] [Algebra B R] [Algebra B W]
  [IsScalarTower B T L] [IsScalarTower B T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R] [Module.FaithfullyFlat T R]
/-- Correct the original mixed unit on the honest Kummer ambient, then
faithfully descend it to a unit of the Kummer solution algebra with both marks. -/
theorem v5KummerReciprocalLift136
    (Δ : N →ₐ[k] N ⊗[k] N) (ε : N →ₐ[k] k)
    (hleft : ∀ n, v5ComponentLeftScalar ε (Δ n) = n)
    (ρ : R →ₐ[T] R ⊗[k] N) (e : R ⊗[T] R ≃ₐ[R] R ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[T] b) = a • ρ b)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R N N
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (pL : L →ₐ[k] k) (pR : R →ₐ[k] k) (pW : W →ₐ[k] C)
    (hT : ∀ t, pL (algebraMap T L t) = pR (algebraMap T R t))
    (hR : ∀ b, algebraMap k C (pR (algebraMap B R b)) = pW (algebraMap B W b))
    (u : (R ⊗[B] W)ˣ) (χ : Nˣ)
    (hχ : Δ (χ : N) = (χ : N) ⊗ₜ[k] (χ : N)) (hε : ε (χ : N) = 1)
    (hu : v5MixedRelativeCoaction (S := W) (ρ.restrictScalars B) (u : R ⊗[B] W) =
      (u : R ⊗[B] W) ⊗ₜ[k] (χ : N)) :
    let hB := v5KummerBaseMarks136 pL pR pW hT hR
    let pS := v5MarkedBaseChangePoint135 pL pR hT
    let pWK := v5MixedMarkedTensor135 pL pW hB
    ∃ v : (L ⊗[T] R)ˣ,
      v5KummerCoaction135 ρ (v : L ⊗[T] R) = (v : L ⊗[T] R) ⊗ₜ[k] (↑χ⁻¹ : N) ∧
      ∃ b : (L ⊗[B] W)ˣ,
        Units.map (Algebra.TensorProduct.includeRight : L ⊗[B] W →ₐ[L]
          (L ⊗[T] R) ⊗[L] (L ⊗[B] W)).toMonoidHom b =
          Units.map (v5KummerAmbientMap136 (k := k) (T := T) (L := L)).toMonoidHom u *
          Units.map (v5OwnMixedInclusion135 (k := k) (L := L)).toMonoidHom
            (v5NormalizeMarkedUnit pS v) ∧
        pWK (b : L ⊗[B] W) = v5MixedMarkedTensor135 pR pW hR (u : R ⊗[B] W) ∧
        pWK (↑b⁻¹ : L ⊗[B] W) = v5MixedMarkedTensor135 pR pW hR (↑u⁻¹ : R ⊗[B] W) := by
  let hB := v5KummerBaseMarks136 pL pR pW hT hR
  let pS := v5MarkedBaseChangePoint135 pL pR hT
  let pWK := v5MixedMarkedTensor135 pL pW hB
  let hmarks := v5KummerTensorMarksCompatible136 pL pR pW hT hB
  let Γ := v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W)
  let uK := Units.map Γ.toMonoidHom u
  letI := v5KummerBaseChangeFaithfullyFlat135 (T := T) (L := L) (R := R)
  obtain ⟨v,hv,hunit⟩ := v5KummerPIDOpposite135 (L := L) Δ ε hleft ρ e he hρ χ hχ hε
  obtain ⟨w,rfl⟩ := hunit
  have huK := v5KummerAmbientUnitWeight136 (L := L) ρ u χ hu
  obtain ⟨b,hprod,hmark,hmarkinv⟩ := v5MixedMarkedChosen136
    (v5KummerCoaction135 ρ) (v5KummerBaseChangeChart135 e)
    (v5KummerBaseChangeChart135_tmul e ρ he) pS pWK hmarks χ uK huK w hv
  refine ⟨w,hv,b,hprod,?_,?_⟩
  · exact hmark.trans (v5KummerAmbientMark136 pL pR pW hT hB hR (u : R ⊗[B] W))
  · exact hmarkinv.trans (v5KummerAmbientMark136 pL pR pW hT hB hR (↑u⁻¹ : R ⊗[B] W))
end StrictEUnit
#print axioms StrictEUnit.v5KummerReciprocalLift136
