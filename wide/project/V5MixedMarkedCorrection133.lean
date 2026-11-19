import V5MarkedWeightNormalization
noncomputable section
namespace StrictEUnit
variable {k R S B C T : Type*}
  [CommRing k] [CommRing R] [CommRing S] [CommRing B] [CommRing C] [CommRing T]
  [Algebra k R] [Algebra k S] [Algebra k B] [Algebra k C] [Algebra k T]

/-- The correcting own unit is normalized at its algebraic mark, while the
mixed unit may have a transcendental complex mark. These are different maps. -/
theorem v5MixedNormalizedCorrection_mark133
    (pR : R →ₐ[k] k) (pS : S →ₐ[k] C) (γ : R →ₐ[k] S)
    (hm : ∀ r, pS (γ r) = algebraMap k C (pR r)) (v : Rˣ) :
    pS (γ (v5NormalizeMarkedUnit pR v : R)) = 1 := by
  rw [hm, v5NormalizeMarkedUnit_mark, map_one]

/-- Descend the corrected mixed unit and preserve both original reciprocal
marks. No algebraicity of the mixed marked value is assumed. -/
theorem v5MixedMarkedReciprocal_descent133
    (pR : R →ₐ[k] k) (pS : S →ₐ[k] C) (pB : B →ₐ[k] C)
    (γ : R →ₐ[k] S)
    (hm : ∀ r, pS (γ r) = algebraMap k C (pR r))
    (φ : B →ₐ[k] S) (hφ : Function.Injective φ)
    (hb : ∀ b, pS (φ b) = pB b)
    (ρ ι : S →ₐ[k] T)
    (hfixed : ∀ s, ρ s = ι s → ∃ b, φ b = s)
    (χ : Tˣ) (u : Sˣ) (v : Rˣ)
    (hu : ρ (u : S) = ι (u : S) * (χ : T))
    (hv : ρ (γ (v5NormalizeMarkedUnit pR v : R)) =
      ι (γ (v5NormalizeMarkedUnit pR v : R)) * (↑χ⁻¹ : T)) :
    ∃ b : Bˣ,
      Units.map φ.toMonoidHom b =
        u * Units.map γ.toMonoidHom (v5NormalizeMarkedUnit pR v) ∧
      pB (b : B) = pS (u : S) ∧
      pB (↑b⁻¹ : B) = pS (↑u⁻¹ : S) := by
  let c := Units.map γ.toMonoidHom (v5NormalizeMarkedUnit pR v)
  let w := u * c
  have hc : pS (c : S) = 1 := v5MixedNormalizedCorrection_mark133 pR pS γ hm v
  have hw : ρ (w : S) = ι (w : S) := by
    change ρ ((u : S) * (c : S)) = ι ((u : S) * (c : S))
    rw [map_mul, map_mul, hu]
    have hv' : ρ (c : S) = ι (c : S) * (↑χ⁻¹ : T) := hv
    rw [hv']
    calc
      _ = (ι (u : S) * ι (c : S)) * ((χ : T) * (↑χ⁻¹ : T)) := by ac_rfl
      _ = _ := by rw [Units.mul_inv, mul_one]
  have hwi : ρ (↑w⁻¹ : S) = ι (↑w⁻¹ : S) := by
    have h : Units.map ρ.toMonoidHom w = Units.map ι.toMonoidHom w := Units.ext hw
    exact congrArg (fun z : Tˣ => (↑z⁻¹ : T)) h
  obtain ⟨a,ha⟩ := hfixed w hw
  obtain ⟨d,hd⟩ := hfixed (↑w⁻¹ : S) hwi
  have had : a * d = 1 := by
    apply hφ
    rw [map_mul,ha,hd,Units.mul_inv,map_one]
  let b : Bˣ := ⟨a,d,had,by rw [mul_comm]; exact had⟩
  have hmapped : Units.map φ.toMonoidHom b = w := Units.ext ha
  have hp : pS (w : S) = pS (u : S) := by
    change pS ((u : S) * (c : S)) = _
    rw [map_mul,hc,mul_one]
  have hpinv : pS (↑w⁻¹ : S) = pS (↑u⁻¹ : S) := by
    have h : Units.map pS.toMonoidHom w = Units.map pS.toMonoidHom u := Units.ext hp
    exact congrArg (fun z : Cˣ => (↑z⁻¹ : C)) h
  refine ⟨b,hmapped,?_,?_⟩
  · change pB a = _
    rw [← hb,ha,hp]
  · change pB d = _
    rw [← hb,hd,hpinv]
end StrictEUnit
#print axioms StrictEUnit.v5MixedNormalizedCorrection_mark133
#print axioms StrictEUnit.v5MixedMarkedReciprocal_descent133
