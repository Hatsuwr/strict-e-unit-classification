import RegularRepresentation

/-!
Transport along an actual equivariant algebra chart. Chart existence is an
input, not constructed here. Pairing compatibility is derived from algebra
multiplication, rather than supplied as an extra assumption.
-/
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit
variable {B R S T U : Type*} [CommRing B] [CommRing R] [CommRing S]
  [CommRing T] [CommRing U] [Algebra B R] [Algebra B S]
  [Algebra B T] [Algebra B U]

/-- Equivariance transports the defining equation of the actual equalizer. -/
theorem chart_weight_iff (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : T) (r : R) :
    r ∈ weightSpace ρ ι χ ↔ e r ∈ weightSpace ρ' ι' (E χ) := by
  change ρ r = ι r * χ ↔ ρ' (e r) = ι' (e r) * E χ
  rw [← hρ, ← hι, ← map_mul, E.injective.eq_iff]

/-- The weight-space equivalence is the restriction of the algebra chart. -/
def chartWeightEquiv (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : T) :
    weightSpace ρ ι χ ≃ₗ[B] weightSpace ρ' ι' (E χ) where
  toFun x := ⟨e x, (chart_weight_iff e E ρ ι ρ' ι' hρ hι χ x).mp x.property⟩
  invFun y := ⟨e.symm y, (chart_weight_iff e E ρ ι ρ' ι' hρ hι χ _).mpr
    (by simpa only [e.apply_symm_apply] using y.property)⟩
  left_inv x := by ext; exact e.symm_apply_apply x
  right_inv y := by ext; exact e.apply_symm_apply y
  map_add' x y := by ext; exact map_add e (x : R) (y : R)
  map_smul' b x := by ext; exact e.toLinearEquiv.map_smul b x

theorem chartWeightEquiv_product (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ ψ : T) (x : weightSpace ρ ι χ) (y : weightSpace ρ ι ψ) :
    e ((x : R) * (y : R)) =
      (chartWeightEquiv e E ρ ι ρ' ι' hρ hι χ x : S) *
      (chartWeightEquiv e E ρ ι ρ' ι' hρ hι ψ y : S) := map_mul e (x : R) (y : R)

/-- Any scalar multiplication pairing on the chart has the same values
as the constructed pairing, after transporting its pure tensors. -/
theorem chart_scalar_pairing_tmul (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r, ρ r = ι r → ∃ b, algebraMap B R b = r)
    (hinj' : Function.Injective (algebraMap B S))
    (hfixed' : ∀ s, ρ' s = ι' s → ∃ b, algebraMap B S b = s)
    (x : weightSpace ρ ι (χ : T)) (y : weightSpace ρ ι (↑χ⁻¹ : T)) :
    scalarWeightPairing ρ ι χ hinj hfixed (x ⊗ₜ[B] y) =
      scalarWeightPairing ρ' ι' (Units.map E.toMonoidHom χ) hinj' hfixed'
        (chartWeightEquiv e E ρ ι ρ' ι' hρ hι (χ : T) x ⊗ₜ[B]
         chartWeightEquiv e E ρ ι ρ' ι' hρ hι (↑χ⁻¹ : T) y) := by
  apply hinj'
  rw [scalarWeightPairing_tmul, ← e.commutes, scalarWeightPairing_tmul]
  exact map_mul e (x : R) (y : R)

/-- Surjectivity of the actual scalar pairing descends through the chart. -/
theorem chart_scalar_pairing_surjective (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : Tˣ)
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r, ρ r = ι r → ∃ b, algebraMap B R b = r)
    (hinj' : Function.Injective (algebraMap B S))
    (hfixed' : ∀ s, ρ' s = ι' s → ∃ b, algebraMap B S b = s)
    (hsurj : Function.Surjective
      (scalarWeightPairing ρ' ι' (Units.map E.toMonoidHom χ) hinj' hfixed')) :
    Function.Surjective (scalarWeightPairing ρ ι χ hinj hfixed) := by
  let F := TensorProduct.congr
    (chartWeightEquiv e E ρ ι ρ' ι' hρ hι (χ : T))
    (chartWeightEquiv e E ρ ι ρ' ι' hρ hι (↑χ⁻¹ : T))
  have heq : scalarWeightPairing ρ ι χ hinj hfixed =
      (scalarWeightPairing ρ' ι' (Units.map E.toMonoidHom χ) hinj' hfixed').comp
        F.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    exact chart_scalar_pairing_tmul e E ρ ι ρ' ι' hρ hι χ hinj hfixed hinj' hfixed' x y
  intro b
  obtain ⟨z, hz⟩ := hsurj b
  refine ⟨F.symm z, ?_⟩
  rw [heq]
  simpa using hz

/-- Pull back a genuine target unit along an equivariant algebra chart.
Its weight equation follows from equivariance; invertibility follows from
the algebra equivalence. -/
theorem chart_weighted_unit
    (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : T) (u : Sˣ) (hu : (u : S) ∈ weightSpace ρ' ι' (E χ)) :
    ∃ v : Rˣ, (v : R) ∈ weightSpace ρ ι χ := by
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, (chart_weight_iff e E ρ ι ρ' ι' hρ hι χ (v : R)).mpr ?_⟩
  change e (e.symm (u : S)) ∈ weightSpace ρ' ι' (E χ)
  simpa only [e.apply_symm_apply] using hu

/-- Product-one witnesses pull back without any scalar-identification
hypothesis. This applies to scalar-extended regular models as well. -/
theorem chart_opposite_product_one
    (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (χ : Tˣ)
    (hex : ∃ x : weightSpace ρ' ι' (E (χ : T)),
      ∃ y : weightSpace ρ' ι' (E (↑χ⁻¹ : T)), (x : S) * (y : S) = 1) :
    ∃ x : weightSpace ρ ι (χ : T),
      ∃ y : weightSpace ρ ι (↑χ⁻¹ : T), (x : R) * (y : R) = 1 := by
  obtain ⟨x, y, hxy⟩ := hex
  refine ⟨(chartWeightEquiv e E ρ ι ρ' ι' hρ hι (χ : T)).symm x,
    (chartWeightEquiv e E ρ ι ρ' ι' hρ hι (↑χ⁻¹ : T)).symm y, ?_⟩
  change e.symm (x : S) * e.symm (y : S) = 1
  rw [← map_mul, hxy, map_one]

theorem chart_base_injective (e : R ≃ₐ[B] S)
    (hinj : Function.Injective (algebraMap B S)) :
    Function.Injective (algebraMap B R) := by
  intro b c h
  apply hinj
  simpa only [e.commutes] using congrArg e h

theorem chart_invariants_are_scalars
    (e : R ≃ₐ[B] S) (E : T ≃ₐ[B] U)
    (ρ ι : R →ₐ[B] T) (ρ' ι' : S →ₐ[B] U)
    (hρ : ∀ r, E (ρ r) = ρ' (e r)) (hι : ∀ r, E (ι r) = ι' (e r))
    (hfixed' : ∀ s, ρ' s = ι' s → ∃ b, algebraMap B S b = s) :
    ∀ r, ρ r = ι r → ∃ b, algebraMap B R b = r := by
  intro r hr
  obtain ⟨b, hb⟩ := hfixed' (e r) (by rw [← hρ, ← hι, hr])
  refine ⟨b, e.injective ?_⟩
  simpa only [e.commutes] using hb

section RegularChart
variable {H : Type*} [CommRing H] [Bialgebra B H]

/-- An equivariant chart to the regular representation pulls a grouplike
unit back to a genuine unit of the specified weight. No invariant-ring
or UFD assumption is needed for this local statement. -/
theorem regular_chart_weighted_unit
    (e : R ≃ₐ[B] H) (E : T ≃ₐ[B] H ⊗[B] H)
    (ρ ι : R →ₐ[B] T)
    (hρ : ∀ r, E (ρ r) = Bialgebra.comulAlgHom B H (e r))
    (hι : ∀ r, E (ι r) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) (e r))
    (χ : Tˣ) (u : Hˣ)
    (hu : Coalgebra.comul (R := B) (u : H) = (u : H) ⊗ₜ[B] (u : H))
    (hχ : E (χ : T) = 1 ⊗ₜ[B] (u : H)) :
    ∃ v : Rˣ, (v : R) ∈ weightSpace ρ ι (χ : T) := by
  let v : Rˣ := Units.map e.symm.toMonoidHom u
  refine ⟨v, (chart_weight_iff e E ρ ι _ _ hρ hι (χ : T) (v : R)).mpr ?_⟩
  change e (e.symm (u : H)) ∈ weightSpace _ _ (E (χ : T))
  rw [e.apply_symm_apply, hχ]
  exact (mem_regularWeightSpace (u : H) (u : H)).mpr hu

/-- The local opposite-weight product-one witnesses are derived from the
regular chart and character, rather than postulated as pairing data. -/
theorem regular_chart_opposite_product_one
    (e : R ≃ₐ[B] H) (E : T ≃ₐ[B] H ⊗[B] H)
    (ρ ι : R →ₐ[B] T)
    (hρ : ∀ r, E (ρ r) = Bialgebra.comulAlgHom B H (e r))
    (hι : ∀ r, E (ι r) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) (e r))
    (χ : Tˣ) (u : Hˣ)
    (hu : Coalgebra.comul (R := B) (u : H) = (u : H) ⊗ₜ[B] (u : H))
    (hχ : E (χ : T) = 1 ⊗ₜ[B] (u : H)) :
    ∃ x : weightSpace ρ ι (χ : T),
      ∃ y : weightSpace ρ ι (↑χ⁻¹ : T), (x : R) * (y : R) = 1 := by
  obtain ⟨v, hv⟩ := regular_chart_weighted_unit e E ρ ι hρ hι χ u hu hχ
  exact ⟨⟨v, hv⟩, ⟨↑v⁻¹, inverse_unit_opposite_weight ρ ι χ v hv⟩, Units.mul_inv v⟩

/-- With scalar identification supplied, the local chart proves
surjectivity of the constructed scalar pairing. -/
theorem regular_chart_scalar_pairing_surjective
    (e : R ≃ₐ[B] H) (E : T ≃ₐ[B] H ⊗[B] H)
    (ρ ι : R →ₐ[B] T)
    (hρ : ∀ r, E (ρ r) = Bialgebra.comulAlgHom B H (e r))
    (hι : ∀ r, E (ι r) =
      (Algebra.TensorProduct.includeLeft : H →ₐ[B] H ⊗[B] H) (e r))
    (χ : Tˣ) (u : Hˣ)
    (hu : Coalgebra.comul (R := B) (u : H) = (u : H) ⊗ₜ[B] (u : H))
    (hχ : E (χ : T) = 1 ⊗ₜ[B] (u : H))
    (hinj : Function.Injective (algebraMap B R))
    (hfixed : ∀ r, ρ r = ι r → ∃ b, algebraMap B R b = r) :
    Function.Surjective (scalarWeightPairing ρ ι χ hinj hfixed) := by
  obtain ⟨x, y, hxy⟩ := regular_chart_opposite_product_one e E ρ ι hρ hι χ u hu hχ
  have hone : scalarWeightPairing ρ ι χ hinj hfixed (x ⊗ₜ[B] y) = 1 := by
    apply hinj
    rw [scalarWeightPairing_tmul, hxy, map_one]
  intro b
  refine ⟨b • (x ⊗ₜ[B] y), ?_⟩
  rw [map_smul, hone, smul_eq_mul, mul_one]
end RegularChart
end StrictEUnit

#print axioms StrictEUnit.chart_weight_iff
#print axioms StrictEUnit.chartWeightEquiv
#print axioms StrictEUnit.chartWeightEquiv_product
#print axioms StrictEUnit.chart_scalar_pairing_tmul
#print axioms StrictEUnit.chart_scalar_pairing_surjective
#print axioms StrictEUnit.regular_chart_weighted_unit
#print axioms StrictEUnit.regular_chart_opposite_product_one
#print axioms StrictEUnit.regular_chart_scalar_pairing_surjective


#print axioms StrictEUnit.chart_opposite_product_one
#print axioms StrictEUnit.chart_base_injective
#print axioms StrictEUnit.chart_invariants_are_scalars

#print axioms StrictEUnit.chart_weighted_unit
