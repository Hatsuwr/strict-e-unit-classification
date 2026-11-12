import TensorUnitFactorization
import TensorUnitCharacterReduction

/-! The proved tensor-unit theorem makes every counit-normalized unit a
character in a commutative domain bialgebra over an algebraically closed
field. Domain of the actual group algebra remains a genuine hypothesis. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H]
  [IsDomain H] [Bialgebra k H]

/-- Counit normalization of any unit in a domain bialgebra is grouplike.
No supplied factorization or supplied character is required. -/
theorem normalized_unit_grouplike_of_domain (u : Hˣ) :
    Coalgebra.comul (R := k) (normalizedRegularUnit (k := k) u : H) =
      (normalizedRegularUnit (k := k) u : H) ⊗ₜ[k]
        (normalizedRegularUnit (k := k) u : H) :=
  normalized_unit_grouplike_of_tensor_units_pure (fun w => tensor_unit_is_pure w) u

/-- Every regular unit has a scalar-times-character decomposition; the scalar
and character are the canonical counit and normalized unit. -/
theorem unit_character_decomposition_of_domain (u : Hˣ) :
    ∃ a : kˣ, ∃ χ : Hˣ,
      Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) ∧
      u = scalarUnit a * χ :=
  ⟨counitUnit (k := k) u, normalizedRegularUnit (k := k) u,
    normalized_unit_grouplike_of_domain u, unit_eq_counit_mul_normalized u⟩

/-- Transport through an actual equivariant chart now derives the character
without a tensor-factorization premise. This is algebraic chart transport,
not a claim that S is the intended numerical E-value ring. -/
theorem chart_unit_character_of_domain
    {S : Type*} [CommRing S] [Algebra k S]
    (e : S ≃ₐ[k] H) (ρ : S →ₐ[k] S ⊗[k] H)
    (hequiv : ∀ s : S, numericalTensorChart e (ρ s) = Coalgebra.comul (R := k) (e s))
    (u : Sˣ) :
    ∃ χ : Hˣ, Coalgebra.comul (R := k) (χ : H) = (χ : H) ⊗ₜ[k] (χ : H) ∧
      ρ (u : S) = (u : S) ⊗ₜ[k] (χ : H) ∧
      normalizedRegularUnit (k := k) (chartUnit e u) = χ :=
  numerical_character_of_tensor_units_pure e ρ hequiv (fun w => tensor_unit_is_pure w) u

end StrictEUnit
#print axioms StrictEUnit.normalized_unit_grouplike_of_domain
#print axioms StrictEUnit.unit_character_decomposition_of_domain
#print axioms StrictEUnit.chart_unit_character_of_domain
