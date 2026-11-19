import NumericalCharacter

/-! A genuine algebraic reduction of the remaining group-unit theorem.
Pure-tensor factorization of comultiplication is an explicit input here.
No theorem asserting that arbitrary tensor-product units factor is claimed. -/
noncomputable section
open scoped TensorProduct
open TensorProduct
namespace StrictEUnit
variable {k H : Type*} [CommRing k] [CommRing H] [Bialgebra k H]

/-- Both counit contractions of an actual pure comultiplication. -/
theorem pure_comultiplication_counit_factors (u a b:H)
    (h : Coalgebra.comul (R:=k) u = a ⊗ₜ[k] b) :
    u = Coalgebra.counit (R:=k) a • b ∧
    u = Coalgebra.counit (R:=k) b • a := by
  constructor
  · have he := congrArg (TensorProduct.lid k H)
      (Coalgebra.rTensor_counit_comul (R:=k) u)
    rw [h, LinearMap.rTensor_tmul] at he
    simpa only [TensorProduct.lid_tmul, one_smul] using he.symm
  · have he := congrArg (TensorProduct.rid k H)
      (Coalgebra.lTensor_counit_comul (R:=k) u)
    rw [h, LinearMap.lTensor_tmul] at he
    simpa only [TensorProduct.rid_tmul, one_smul] using he.symm

/-- A counit-one element whose comultiplication is actually pure is grouplike.
The two pure factors need not separately be assumed invertible. -/
theorem grouplike_of_counit_one_pure_comultiplication (u a b:H)
    (hc : Coalgebra.counit (R:=k) u = 1)
    (h : Coalgebra.comul (R:=k) u = a ⊗ₜ[k] b) :
    Coalgebra.comul (R:=k) u = u ⊗ₜ[k] u := by
  obtain ⟨hl,hr⟩ := pure_comultiplication_counit_factors u a b h
  have hab : Coalgebra.counit (R:=k) b * Coalgebra.counit (R:=k) a = 1 := by
    have he := congrArg (Coalgebra.counit (R:=k)) hr
    simpa only [hc, map_smul, smul_eq_mul] using he.symm
  rw [h]
  calc
    a ⊗ₜ[k] b = (Coalgebra.counit (R:=k) b * Coalgebra.counit (R:=k) a) •
      (a ⊗ₜ[k] b) := by rw [hab, one_smul]
    _ = (Coalgebra.counit (R:=k) b • a) ⊗ₜ[k]
      (Coalgebra.counit (R:=k) a • b) := by
      simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, mul_comm]
    _ = u ⊗ₜ[k] u := by rw [← hr, ← hl]

/-- Canonical normalization becomes a character if actual comultiplication
admits pure-tensor factorization. Existence of that factorization is not proved. -/
theorem normalized_unit_grouplike_of_pure_comultiplication (u:Hˣ)
    (a b:H) (h : Coalgebra.comul (R:=k) (u:H) = a ⊗ₜ[k] b) :
    Coalgebra.comul (R:=k) (normalizedRegularUnit (k:=k) u : H) =
      (normalizedRegularUnit (k:=k) u : H) ⊗ₜ[k]
        (normalizedRegularUnit (k:=k) u : H) := by
  have hn : (normalizedRegularUnit (k:=k) u : H) =
      (↑(counitUnit (k:=k) u)⁻¹ : k) • (u:H) := by
    change algebraMap k H (↑(counitUnit (k:=k) u)⁻¹ : k) * (u:H) = _
    exact (Algebra.smul_def _ _).symm
  apply grouplike_of_counit_one_pure_comultiplication
    (normalizedRegularUnit (k:=k) u : H)
    ((↑(counitUnit (k:=k) u)⁻¹ : k) • a) b
  · exact congrArg (fun x:kˣ => (x:k)) (normalizedRegularUnit_counit u)
  · rw [hn, map_smul, h, TensorProduct.smul_tmul']
/-- The sole missing geometric input can be isolated as a statement about
units of the actual tensor-product algebra, rather than assumed characters. -/
theorem normalized_unit_grouplike_of_tensor_units_pure
    (hfactor : ∀ w : (H ⊗[k] H)ˣ, ∃ a b:H, (w:H ⊗[k] H) = a ⊗ₜ[k] b)
    (u:Hˣ) :
    Coalgebra.comul (R:=k) (normalizedRegularUnit (k:=k) u : H) =
      (normalizedRegularUnit (k:=k) u : H) ⊗ₜ[k]
        (normalizedRegularUnit (k:=k) u : H) := by
  obtain ⟨a,b,hab⟩ := hfactor (Units.map (Bialgebra.comulAlgHom k H).toMonoidHom u)
  exact normalized_unit_grouplike_of_pure_comultiplication u a b hab

/-- Exact scalar-times-normalized-unit identity, independent of character existence. -/
theorem unit_eq_counit_mul_normalized (u:Hˣ) :
    u = scalarUnit (counitUnit (k:=k) u) * normalizedRegularUnit (k:=k) u := by
  simp only [normalizedRegularUnit, scalarUnit, map_inv, mul_inv_cancel_left]

/-- The actual numerical semi-invariance follows from the concrete tensor-unit
factorization input and a supplied equivariant chart. The factorization theorem
and identification of the actual numerical value ring remain unproved here. -/
theorem numerical_character_of_tensor_units_pure
    {S : Type*} [CommRing S] [Algebra k S]
    (e:S ≃ₐ[k] H) (ρ:S →ₐ[k] S ⊗[k] H)
    (hequiv:∀ s:S, numericalTensorChart e (ρ s) = Coalgebra.comul (R:=k) (e s))
    (hfactor : ∀ w : (H ⊗[k] H)ˣ, ∃ a b:H, (w:H ⊗[k] H) = a ⊗ₜ[k] b)
    (u:Sˣ) :
    ∃ χ:Hˣ, Coalgebra.comul (R:=k) (χ:H) = (χ:H) ⊗ₜ[k] (χ:H) ∧
      ρ (u:S) = (u:S) ⊗ₜ[k] (χ:H) ∧
      normalizedRegularUnit (k:=k) (chartUnit e u) = χ := by
  apply numerical_character_of_unit_decomposition e ρ hequiv u
  exact ⟨counitUnit (k:=k) (chartUnit e u),
    normalizedRegularUnit (k:=k) (chartUnit e u),
    normalized_unit_grouplike_of_tensor_units_pure hfactor (chartUnit e u),
    unit_eq_counit_mul_normalized (chartUnit e u)⟩

end StrictEUnit
#print axioms StrictEUnit.pure_comultiplication_counit_factors
#print axioms StrictEUnit.grouplike_of_counit_one_pure_comultiplication
#print axioms StrictEUnit.normalized_unit_grouplike_of_pure_comultiplication
#print axioms StrictEUnit.normalized_unit_grouplike_of_tensor_units_pure
#print axioms StrictEUnit.unit_eq_counit_mul_normalized
#print axioms StrictEUnit.numerical_character_of_tensor_units_pure
