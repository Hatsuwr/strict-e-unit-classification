import V5MixedMarkedCorrection133
noncomputable section
namespace StrictEUnit
variable {k R S B C T U : Type*}
  [CommRing k] [CommRing R] [CommRing S] [CommRing B] [CommRing C]
  [CommRing T] [CommRing U]
  [Algebra k R] [Algebra k S] [Algebra k B] [Algebra k C]
  [Algebra k T] [Algebra k U]

/-- Own opposite weight transports to the mixed action after algebraic
normalization. No mixed mark is required to be algebraic. -/
theorem v5OwnCorrectionTransport134
    (pR : R →ₐ[k] k) (γ : R →ₐ[k] S)
    (ρR ιR : R →ₐ[k] U) (ρS ιS : S →ₐ[k] T) (ψ : U →ₐ[k] T)
    (hρ : ∀ r, ρS (γ r) = ψ (ρR r))
    (hι : ∀ r, ιS (γ r) = ψ (ιR r))
    (χ : Uˣ) (v : Rˣ)
    (hv : ρR (v : R) = ιR (v : R) * (↑χ⁻¹ : U)) :
    ρS (γ (v5NormalizeMarkedUnit pR v : R)) =
      ιS (γ (v5NormalizeMarkedUnit pR v : R)) *
        (↑(Units.map ψ.toMonoidHom χ)⁻¹ : T) := by
  rw [hρ, v5NormalizeMarkedUnit_weight pR ρR ιR (↑χ⁻¹ : U) v hv,
    map_mul, ← hι]
  rfl

/-- A correcting eigenunit produced by PID line descent, together with the
equivariant own-to-mixed maps, suffices for exact marked reciprocal descent.
The normalized weight equation is proved here rather than assumed. -/
theorem v5MixedReciprocalFromOwnEigenunit134
    (pR : R →ₐ[k] k) (pS : S →ₐ[k] C) (pB : B →ₐ[k] C)
    (γ : R →ₐ[k] S) (hm : ∀ r, pS (γ r) = algebraMap k C (pR r))
    (φ : B →ₐ[k] S) (hφ : Function.Injective φ)
    (hb : ∀ b, pS (φ b) = pB b)
    (ρR ιR : R →ₐ[k] U) (ρS ιS : S →ₐ[k] T) (ψ : U →ₐ[k] T)
    (hρ : ∀ r, ρS (γ r) = ψ (ρR r))
    (hι : ∀ r, ιS (γ r) = ψ (ιR r))
    (hfixed : ∀ s, ρS s = ιS s → ∃ b, φ b = s)
    (χ : Uˣ) (u : Sˣ)
    (hu : ρS (u : S) = ιS (u : S) * ψ (χ : U))
    (hown : ∃ v : R, ρR v = ιR v * (↑χ⁻¹ : U) ∧ IsUnit v) :
    ∃ v : Rˣ, ∃ b : Bˣ,
      Units.map φ.toMonoidHom b =
        u * Units.map γ.toMonoidHom (v5NormalizeMarkedUnit pR v) ∧
      pB (b : B) = pS (u : S) ∧
      pB (↑b⁻¹ : B) = pS (↑u⁻¹ : S) := by
  obtain ⟨v,hv,hunit⟩ := hown
  obtain ⟨w,rfl⟩ := hunit
  refine ⟨w, ?_⟩
  exact v5MixedMarkedReciprocal_descent133 pR pS pB γ hm φ hφ hb ρS ιS hfixed
    (Units.map ψ.toMonoidHom χ) u w hu
    (v5OwnCorrectionTransport134 pR γ ρR ιR ρS ιS ψ hρ hι χ w hv)

end StrictEUnit
#print axioms StrictEUnit.v5OwnCorrectionTransport134
#print axioms StrictEUnit.v5MixedReciprocalFromOwnEigenunit134
