import RegularRepresentation

/-!
# Numerical character extraction under an explicit unit-decomposition input

This file does NOT prove the connected-group unit theorem of Rosenlicht/Milne,
existence of a rational torsor point, or existence of a torsor chart. For a given
unit its scalar-times-grouplike decomposition is an explicit hypothesis. We
prove its canonical counit normalization, uniqueness, and transport of its
actual semi-invariance equation through a supplied equivariant chart.

The chart on tensor products is constructed, not assumed to preserve pure
tensors. No E-value ring is identified with these abstract algebras here.
-/

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit

variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

/-- An actual scalar unit in the bialgebra. -/
def scalarUnit (a : kˣ) : Hˣ := Units.map (algebraMap k H).toMonoidHom a

/-- The counit of a unit is an actual unit, not just a nonzero scalar. -/
def counitUnit (u : Hˣ) : kˣ :=
  Units.map (Bialgebra.counitAlgHom k H).toMonoidHom u

@[simp] theorem counitUnit_coe (u : Hˣ) :
    (counitUnit (k := k) u : k) = Coalgebra.counit (R := k) (u : H) := rfl

/-- This applies to the abstract algebraic point/counit, not the original
numerical embedding of the value algebra. -/
theorem counit_of_unit_ne_zero [Nontrivial k] (u : Hˣ) :
    Coalgebra.counit (R := k) (u : H) ≠ 0 := (counitUnit (k := k) u).ne_zero

@[simp] theorem counitUnit_scalarUnit (a : kˣ) :
    counitUnit (k := k) (scalarUnit (H := H) a) = a := by
  apply Units.ext
  exact Bialgebra.counit_algebraMap (R := k) (A := H) (a : k)

/-- Normalize a unit by its value at the identity. -/
def normalizedRegularUnit (u : Hˣ) : Hˣ :=
  scalarUnit (counitUnit (k := k) u)⁻¹ * u

/-- Normalization always makes the counit one, without a decomposition
hypothesis. -/
theorem normalizedRegularUnit_counit (u : Hˣ) :
    counitUnit (k := k) (normalizedRegularUnit (k := k) u) = 1 := by
  change (Units.map (Bialgebra.counitAlgHom k H).toMonoidHom)
    (scalarUnit (counitUnit (k := k) u)⁻¹ * u) = 1
  rw [map_mul]
  change counitUnit (k := k) (scalarUnit (counitUnit (k := k) u)⁻¹) *
    counitUnit (k := k) u = 1
  rw [counitUnit_scalarUnit]
  exact inv_mul_cancel _

/-- Multiplying a regular function by any base unit does not change its
canonical normalized factor. This holds even without a grouplike assumption. -/
theorem normalizedRegularUnit_scalar_invariant (a : kˣ) (u : Hˣ) :
    normalizedRegularUnit (k := k) (scalarUnit a * u) =
      normalizedRegularUnit (k := k) u := by
  have hc : counitUnit (k := k) (scalarUnit a * u) = a * counitUnit (k := k) u := by
    change (Units.map (Bialgebra.counitAlgHom k H).toMonoidHom) (scalarUnit a * u) = _
    rw [map_mul]
    change counitUnit (k := k) (scalarUnit a) * counitUnit (k := k) u = _
    rw [counitUnit_scalarUnit]
  unfold normalizedRegularUnit
  rw [hc]
  simp only [scalarUnit, map_mul, map_inv, mul_inv_rev]
  simp only [mul_assoc, inv_mul_cancel_left]

/-- In a scalar-times-character decomposition, the scalar is necessarily
the counit of the given unit. -/
theorem counitUnit_eq_of_decomposition (u : Hˣ) (a : kˣ) (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hdecomp : u = scalarUnit a * χ) : counitUnit (k := k) u = a := by
  apply Units.ext
  change Coalgebra.counit (R := k) (u : H) = (a : k)
  rw [hdecomp]
  change Coalgebra.counit (R := k) (algebraMap k H (a : k) * (χ : H)) = (a : k)
  rw [Bialgebra.counit_mul, Bialgebra.counit_algebraMap,
    counit_grouplike_unit_eq_one χ hχ, mul_one]

/-- Thus normalization recovers exactly the character in any such
decomposition. The decomposition itself is NOT asserted to exist. -/
theorem normalizedRegularUnit_eq_of_decomposition (u : Hˣ) (a : kˣ) (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hdecomp : u = scalarUnit a * χ) : normalizedRegularUnit (k := k) u = χ := by
  unfold normalizedRegularUnit
  rw [counitUnit_eq_of_decomposition u a χ hχ hdecomp, hdecomp]
  simp only [scalarUnit, map_inv, inv_mul_cancel_left]

/-- The character is independent of the particular scalar-times-character
decomposition of a fixed regular function. -/
theorem grouplike_factor_unique (u : Hˣ) (a b : kˣ) (χ ψ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hψ : Coalgebra.comul (R := k) (ψ : H) = (ψ : H) ⊗ₜ[k] (ψ : H))
    (huχ : u = scalarUnit a * χ) (huψ : u = scalarUnit b * ψ) : χ = ψ :=
  (normalizedRegularUnit_eq_of_decomposition u a χ hχ huχ).symm.trans
    (normalizedRegularUnit_eq_of_decomposition u b ψ hψ huψ)

/-- A supplied decomposition gives the actual regular-representation
semi-invariance identity. -/
theorem regular_unit_semivariant_of_decomposition (u : Hˣ) (a : kˣ) (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hdecomp : u = scalarUnit a * χ) :
    Coalgebra.comul (R := k) (u : H) = (u : H) ⊗ₜ[k] (χ : H) := by
  apply (regular_weight_iff_scalar_multiple (χ : H) (u : H) hχ).mpr
  refine ⟨(a : k), ?_⟩
  rw [hdecomp]
  change algebraMap k H (a : k) * (χ : H) = (a : k) • (χ : H)
  exact (Algebra.smul_def _ _).symm

section Chart
variable {S : Type*} [CommRing S] [Algebra k S]

/-- The actual tensor extension of a numerical torsor chart. -/
def numericalTensorChart (e : S ≃ₐ[k] H) : S ⊗[k] H ≃ₐ[k] H ⊗[k] H :=
  Algebra.TensorProduct.congr e (AlgEquiv.refl : H ≃ₐ[k] H)

@[simp] theorem numericalTensorChart_tmul (e : S ≃ₐ[k] H) (s : S) (h : H) :
    numericalTensorChart e (s ⊗ₜ[k] h) = e s ⊗ₜ[k] h := rfl

/-- The chart sends a unit to an actual unit. -/
def chartUnit (e : S ≃ₐ[k] H) (u : Sˣ) : Hˣ := Units.map e.toMonoidHom u

/-- Equation (15) follows from the explicit unit-decomposition input and
actual equivariance of the chart. Connectedness and the theorem furnishing
the decomposition remain separate mathematical obligations. -/
theorem numerical_unit_semivariant_of_decomposition
    (e : S ≃ₐ[k] H) (ρ : S →ₐ[k] S ⊗[k] H)
    (hequiv : ∀ s : S, numericalTensorChart e (ρ s) =
      Coalgebra.comul (R := k) (e s))
    (u : Sˣ) (a : kˣ) (χ : Hˣ)
    (hχ : Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H))
    (hdecomp : chartUnit e u = scalarUnit a * χ) :
    ρ (u : S) = (u : S) ⊗ₜ[k] (χ : H) := by
  apply (numericalTensorChart e).injective
  rw [hequiv, numericalTensorChart_tmul]
  exact regular_unit_semivariant_of_decomposition (chartUnit e u) a χ hχ hdecomp

/-- Existential packaging leaves exactly the given decomposition as an
input, rather than assuming the desired numerical semi-invariance. -/
theorem numerical_character_of_unit_decomposition
    (e : S ≃ₐ[k] H) (ρ : S →ₐ[k] S ⊗[k] H)
    (hequiv : ∀ s : S, numericalTensorChart e (ρ s) =
      Coalgebra.comul (R := k) (e s)) (u : Sˣ)
    (hdecomp : ∃ a : kˣ, ∃ χ : Hˣ,
      Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) ∧
      chartUnit e u = scalarUnit a * χ) :
    ∃ χ : Hˣ,
      Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) ∧
      ρ (u : S) = (u : S) ⊗ₜ[k] (χ : H) ∧
      normalizedRegularUnit (k := k) (chartUnit e u) = χ := by
  obtain ⟨a, χ, hχ, hu⟩ := hdecomp
  exact ⟨χ, hχ, numerical_unit_semivariant_of_decomposition e ρ hequiv u a χ hχ hu,
    normalizedRegularUnit_eq_of_decomposition (chartUnit e u) a χ hχ hu⟩

end Chart

section CharacterUniqueness
variable {B R C : Type*} [CommRing B] [CommRing R] [CommRing C]
  [Algebra B R] [Algebra B C]

/-- An actual algebraic point detects the right tensor factor when the left
factor is a unit. Its scalar value is a unit, so cancellation is valid even
when the base is not a field. Point existence is not assumed automatically. -/
theorem right_tensor_factor_unique_at_point
    (p : R →ₐ[B] B) (u : Rˣ) (χ ψ : C)
    (h : (u : R) ⊗ₜ[B] χ = (u : R) ⊗ₜ[B] ψ) : χ = ψ := by
  have hp := congrArg (TensorProduct.lid B C)
    (congrArg (p.toLinearMap.rTensor C) h)
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul] at hp
  let a : Bˣ := Units.map p.toMonoidHom u
  change (a : B) • χ = (a : B) • ψ at hp
  have hc := congrArg (fun x : C => (↑a⁻¹ : B) • x) hp
  simpa only [smul_smul, Units.inv_mul, one_smul] using hc

/-- A fixed unit has at most one character in its actual semi-invariance
identity. Consequently two different choices of torsor point or chart cannot
change that character once they yield such identities for the same coaction.
The supplied point is used only to justify tensor cancellation. -/
theorem numerical_character_unique_at_point
    (p : R →ₐ[B] B) (ρ : R →ₐ[B] R ⊗[B] C)
    (u : Rˣ) (χ ψ : C)
    (hχ : ρ (u : R) = (u : R) ⊗ₜ[B] χ)
    (hψ : ρ (u : R) = (u : R) ⊗ₜ[B] ψ) : χ = ψ :=
  right_tensor_factor_unique_at_point p u χ ψ (hχ.symm.trans hψ)

end CharacterUniqueness
end StrictEUnit

#print axioms StrictEUnit.counitUnit_coe
#print axioms StrictEUnit.counit_of_unit_ne_zero
#print axioms StrictEUnit.counitUnit_scalarUnit
#print axioms StrictEUnit.normalizedRegularUnit_counit
#print axioms StrictEUnit.normalizedRegularUnit_scalar_invariant
#print axioms StrictEUnit.counitUnit_eq_of_decomposition
#print axioms StrictEUnit.normalizedRegularUnit_eq_of_decomposition
#print axioms StrictEUnit.grouplike_factor_unique
#print axioms StrictEUnit.regular_unit_semivariant_of_decomposition
#print axioms StrictEUnit.numericalTensorChart_tmul
#print axioms StrictEUnit.numerical_unit_semivariant_of_decomposition
#print axioms StrictEUnit.numerical_character_of_unit_decomposition

#print axioms StrictEUnit.right_tensor_factor_unique_at_point
#print axioms StrictEUnit.numerical_character_unique_at_point
#print axioms StrictEUnit.scalarUnit
#print axioms StrictEUnit.counitUnit
#print axioms StrictEUnit.normalizedRegularUnit
#print axioms StrictEUnit.numericalTensorChart
#print axioms StrictEUnit.chartUnit
