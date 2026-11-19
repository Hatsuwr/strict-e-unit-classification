import V5OwnCorrectionTransport134
import V5OwnMixedMaps135
import V5MixedMarkedTensor135
import V5MixedInvariantDescent135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k L S W N C : Type*}
  [Field k] [CommRing L] [CommRing S] [CommRing W] [CommRing N] [CommRing C]
  [Algebra k L] [Algebra k S] [Algebra L S] [IsScalarTower k L S]
  [Algebra k W] [Algebra L W] [IsScalarTower k L W] [Algebra k N] [Algebra k C]
  [Module.FaithfullyFlat L S]
/-- With a natural torsor chart, every own correcting eigenunit gives exact
mixed reciprocal descent; equivariance, marks, injection and invariant image
are derived, rather than supplied as separate hypotheses. -/
theorem v5MixedMarkedChosen136
    (ρ : S →ₐ[L] S ⊗[k] N) (e : S ⊗[L] S ≃ₐ[S] S ⊗[k] N)
    (he : ∀ a b, e (a ⊗ₜ[L] b) = a • ρ b)
    (pS : S →ₐ[k] k) (pW : W →ₐ[k] C)
    (hm : ∀ l, algebraMap k C (pS (algebraMap L S l)) = pW (algebraMap L W l))
    (χ : Nˣ) (u : (S ⊗[L] W)ˣ)
    (hu : v5MixedRelativeCoaction ρ (u : S ⊗[L] W) =
      (u : S ⊗[L] W) ⊗ₜ[k] (χ : N))
    (v : Sˣ) (hv : ρ (v : S) = (v : S) ⊗ₜ[k] (↑χ⁻¹ : N)) :
    ∃ b : Wˣ,
      Units.map (Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W).toMonoidHom b =
        u * Units.map (v5OwnMixedInclusion135 (k := k) (L := L) (S := S) (W := W)).toMonoidHom
          (v5NormalizeMarkedUnit pS v) ∧
      pW (b : W) = v5MixedMarkedTensor135 pS pW hm (u : S ⊗[L] W) ∧
      pW (↑b⁻¹ : W) = v5MixedMarkedTensor135 pS pW hm (↑u⁻¹ : S ⊗[L] W) := by
  let γ := v5OwnMixedInclusion135 (k := k) (L := L) (S := S) (W := W)
  let ψ := v5OwnMixedTensorMap135 (k := k) (L := L) (S := S) (W := W) (N := N)
  let χU : (S ⊗[k] N)ˣ :=
    Units.map (Algebra.TensorProduct.includeRight : N →ₐ[k] S ⊗[k] N).toMonoidHom χ
  have hu' : v5MixedRelativeCoaction ρ (u : S ⊗[L] W) =
      (Algebra.TensorProduct.includeLeft : S ⊗[L] W →ₐ[k] (S ⊗[L] W) ⊗[k] N)
        (u : S ⊗[L] W) * ψ (χU : S ⊗[k] N) := by
    change v5MixedRelativeCoaction ρ (u : S ⊗[L] W) =
      ((u : S ⊗[L] W) ⊗ₜ[k] 1) * (γ (1 : S) ⊗ₜ[k] (χ : N))
    rw [map_one, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact hu
  have hv' : (ρ.restrictScalars k) (v : S) =
      (Algebra.TensorProduct.includeLeft : S →ₐ[k] S ⊗[k] N) (v : S) *
        (↑χU⁻¹ : S ⊗[k] N) := by
    change ρ (v : S) = ((v : S) ⊗ₜ[k] (1 : N)) * ((1 : S) ⊗ₜ[k] (↑χ⁻¹ : N))
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    exact hv
  let fixed := v5_mixed_exact_invariant_image135 (W := W) ρ e he
  have hcorr := v5OwnCorrectionTransport134 pS γ
    (ρ.restrictScalars k) Algebra.TensorProduct.includeLeft
    (v5MixedRelativeCoaction ρ) Algebra.TensorProduct.includeLeft ψ
    (v5OwnMixedCoaction135 ρ) v5OwnMixedTrivial135 χU v hv'
  exact v5MixedMarkedReciprocal_descent133 pS (v5MixedMarkedTensor135 pS pW hm) pW γ
    (v5MixedMarkedTensor135_includeLeft pS pW hm)
    ((Algebra.TensorProduct.includeRight : W →ₐ[L] S ⊗[L] W).restrictScalars k)
    fixed.1 (v5MixedMarkedTensor135_includeRight pS pW hm)
    (v5MixedRelativeCoaction ρ) Algebra.TensorProduct.includeLeft fixed.2
    (Units.map ψ.toMonoidHom χU) u v hu' hcorr
end StrictEUnit
#print axioms StrictEUnit.v5MixedMarkedChosen136
