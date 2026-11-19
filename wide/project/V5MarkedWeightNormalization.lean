import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section
namespace StrictEUnit
variable {k B S T : Type*} [CommRing k] [CommRing B] [CommRing S] [CommRing T]
  [Algebra k B] [Algebra k S] [Algebra k T]

/-- Normalize an actual unit by its marked value, using a scalar unit rather
than division in the ambient ring. -/
def v5NormalizeMarkedUnit (p : S →ₐ[k] k) (v : Sˣ) : Sˣ :=
  Units.map (algebraMap k S).toMonoidHom (Units.map p.toMonoidHom v)⁻¹ * v

@[simp] theorem v5NormalizeMarkedUnit_mark (p : S →ₐ[k] k) (v : Sˣ) :
    p (v5NormalizeMarkedUnit p v : S) = 1 := by
  change p (algebraMap k S (↑(Units.map p.toMonoidHom v)⁻¹ : k) * (v : S)) = 1
  rw [map_mul, p.commutes]
  change (↑(Units.map p.toMonoidHom v)⁻¹ : k) * (Units.map p.toMonoidHom v : k) = 1
  exact Units.inv_mul _

/-- Scalar normalization preserves the literal weight equation. -/
theorem v5NormalizeMarkedUnit_weight
    (p : S →ₐ[k] k) (ρ ι : S →ₐ[k] T) (χ : T) (v : Sˣ)
    (hv : ρ (v : S) = ι (v : S) * χ) :
    ρ (v5NormalizeMarkedUnit p v : S) = ι (v5NormalizeMarkedUnit p v : S) * χ := by
  change ρ (algebraMap k S _ * (v : S)) = ι (algebraMap k S _ * (v : S)) * χ
  rw [map_mul, map_mul, ρ.commutes, ι.commutes, hv, mul_assoc]

/-- The original unit's marked value is unchanged by multiplying by the
normalized opposite-weight lift. -/
theorem v5NormalizedProduct_mark (p : S →ₐ[k] k) (u v : Sˣ) :
    p ((u * v5NormalizeMarkedUnit p v : Sˣ) : S) = p (u : S) := by
  change p ((u : S) * (v5NormalizeMarkedUnit p v : S)) = _
  rw [map_mul, v5NormalizeMarkedUnit_mark, mul_one]

/-- Opposite characters cancel after marked normalization. -/
theorem v5NormalizedProduct_invariant
    (p : S →ₐ[k] k) (ρ ι : S →ₐ[k] T) (χ : Tˣ) (u v : Sˣ)
    (hu : ρ (u : S) = ι (u : S) * (χ : T))
    (hv : ρ (v : S) = ι (v : S) * (↑χ⁻¹ : T)) :
    ρ ((u * v5NormalizeMarkedUnit p v : Sˣ) : S) =
      ι ((u * v5NormalizeMarkedUnit p v : Sˣ) : S) := by
  have hn := v5NormalizeMarkedUnit_weight p ρ ι (↑χ⁻¹ : T) v hv
  change ρ ((u : S) * (v5NormalizeMarkedUnit p v : S)) = _
  rw [map_mul, hu, hn]
  change (ι (u : S) * (χ : T)) * (ι (v5NormalizeMarkedUnit p v : S) * (↑χ⁻¹ : T)) =
    ι ((u : S) * (v5NormalizeMarkedUnit p v : S))
  rw [map_mul]
  calc
    _ = (ι (u : S) * ι (v5NormalizeMarkedUnit p v : S)) * ((χ : T) * (↑χ⁻¹ : T)) := by ac_rfl
    _ = _ := by rw [Units.mul_inv, mul_one]

/-- Exact invariant descent retains both the unit and the original marked
value. The base B may be the actual Laurent algebra and its mark t↦1. -/
theorem v5NormalizedProduct_descends_with_mark
    (p : S →ₐ[k] k) (pB : B →ₐ[k] k) (φ : B →ₐ[k] S)
    (hφ : Function.Injective φ) (hmark : ∀ b, p (φ b) = pB b)
    (ρ ι : S →ₐ[k] T)
    (hfixed : ∀ s, ρ s = ι s → ∃ b, φ b = s)
    (χ : Tˣ) (u v : Sˣ)
    (hu : ρ (u : S) = ι (u : S) * (χ : T))
    (hv : ρ (v : S) = ι (v : S) * (↑χ⁻¹ : T)) :
    ∃ b : Bˣ, Units.map φ.toMonoidHom b = u * v5NormalizeMarkedUnit p v ∧
      pB (b : B) = p (u : S) := by
  let w := u * v5NormalizeMarkedUnit p v
  have hw : ρ (w : S) = ι (w : S) := v5NormalizedProduct_invariant p ρ ι χ u v hu hv
  have hwi : ρ (↑w⁻¹ : S) = ι (↑w⁻¹ : S) := by
    have he : Units.map ρ.toMonoidHom w = Units.map ι.toMonoidHom w := Units.ext hw
    exact congrArg (fun z : Tˣ => (↑z⁻¹ : T)) he
  obtain ⟨a, ha⟩ := hfixed w hw
  obtain ⟨c, hc⟩ := hfixed (↑w⁻¹ : S) hwi
  have hac : a * c = 1 := by
    apply hφ
    rw [map_mul, ha, hc, Units.mul_inv, map_one]
  let b : Bˣ := ⟨a, c, hac, by rw [mul_comm]; exact hac⟩
  refine ⟨b, Units.ext ha, ?_⟩
  change pB a = _
  rw [← hmark, ha]
  exact v5NormalizedProduct_mark p u v

/-- The reciprocal marked value is preserved as well, using equality in
the unit group rather than dividing by a possibly zero scalar. -/
theorem v5NormalizedProduct_inverse_mark (p : S →ₐ[k] k) (u v : Sˣ) :
    p (↑(u * v5NormalizeMarkedUnit p v)⁻¹ : S) = p (↑u⁻¹ : S) := by
  have he : Units.map p.toMonoidHom (u * v5NormalizeMarkedUnit p v) =
      Units.map p.toMonoidHom u := Units.ext (v5NormalizedProduct_mark p u v)
  exact congrArg (fun z : kˣ => (↑z⁻¹ : k)) he

end StrictEUnit
#print axioms StrictEUnit.v5NormalizeMarkedUnit_mark
#print axioms StrictEUnit.v5NormalizeMarkedUnit_weight
#print axioms StrictEUnit.v5NormalizedProduct_mark
#print axioms StrictEUnit.v5NormalizedProduct_invariant
#print axioms StrictEUnit.v5NormalizedProduct_descends_with_mark

#print axioms StrictEUnit.v5NormalizedProduct_inverse_mark
