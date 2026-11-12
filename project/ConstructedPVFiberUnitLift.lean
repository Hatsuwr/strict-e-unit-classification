import FiberUnitComparison
import ConstructedPVCharacterLift

/-! Comparison of an abstract algebraic-fiber unit with a lifted regular
functional unit. Tensor-unit factorization remains an explicit unproved
geometric input. No numerical specialization/Beukers assertion is made. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule

/-- Assemble fiber character extraction, a supplied functional character lift,
and scalar comparison while the bialgebra is still an abstract instance.
The constructed case below supplies every additional input internally. -/
private theorem fiber_unit_lift_from_character_lifts
    {k B R H : Type*} [Field k] [IsAlgClosed k]
    [CommRing B] [CommRing R] [CommRing H] [Bialgebra k H]
    [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
    [Algebra B k] [IsScalarTower k B k]
    [Module.FaithfullyFlat B R] [Algebra.FiniteType B R]
    (d : Derivation k R R)
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (hco : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((inverseMultiplicationCoaction e).restrictScalars k)
        (AlgHom.id k H) (inverseMultiplicationCoaction e r)) =
      weightBaseChangeAlgHom (B := k) (R := H) (T := H ⊗[k] H) R
        (Bialgebra.comulAlgHom k H) (inverseMultiplicationCoaction e r))
    (hlift : ∀ χ:Hˣ,
      Coalgebra.comul (R:=k) (χ:H) = (χ:H) ⊗ₜ[k] (χ:H) →
      ∃ v:Rˣ, ∃ b:B,
        inverseMultiplicationCoaction e (v:R) = (v:R) ⊗ₜ[k] (χ:H) ∧
        d (v:R) = algebraMap B R b * (v:R))
    (hfactor : ∀ w:(H ⊗[k] H)ˣ, ∃ a b:H, (w:H ⊗[k] H)=a ⊗ₜ[k] b)
    (u:(k ⊗[B] R)ˣ) :
    ∃ χ:Hˣ, ∃ v:Rˣ, ∃ b:B, ∃ a:kˣ,
      Coalgebra.comul (R:=k) (χ:H)=(χ:H) ⊗ₜ[k] (χ:H) ∧
      inverseMultiplicationCoaction e (v:R)=(v:R) ⊗ₜ[k] (χ:H) ∧
      d (v:R)=algebraMap B R b * (v:R) ∧
      u = Units.map (algebraMap k (k ⊗[B] R)).toMonoidHom a *
        Units.map (algebraicFiberSpecialization (k:=k) (B:=B) (R:=R)).toMonoidHom v := by
  let chart := algebraicFiberTrivialization e
  have hchart := algebraicFiberTrivialization_coaction e hco
  obtain ⟨χ,hχ,hu,_⟩ := numerical_character_of_tensor_units_pure chart
    (algebraicFiberCoaction e) hchart hfactor u
  obtain ⟨v,b,hv,hdb⟩ := hlift χ hχ
  let vS := Units.map (algebraicFiberSpecialization (k:=k) (B:=B) (R:=R)).toMonoidHom v
  have hvS : algebraicFiberCoaction e (vS:k ⊗[B] R) =
      (vS:k ⊗[B] R) ⊗ₜ[k] (χ:H) :=
    algebraicFiberSpecialization_weight e (v:R) (χ:H) hv
  obtain ⟨a,ha⟩ := chart_same_weight_units_scalar_ratio chart (algebraicFiberCoaction e)
    hchart u vS χ hu hvS
  exact ⟨χ,v,b,a,hχ,hv,hdb,ha⟩

variable {k B R : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
  [UniqueFactorizationMonoid B] [CommRing R] [IsDomain R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra B k] [IsScalarTower k B k]
  [Module.FaithfullyFlat B R] [Algebra.FiniteType B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "e" => AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he
local notation "ρ" => inverseMultiplicationCoaction e
local notation "Δ" => pvConstantComultiplication dB d hb he hc

/-- Under the precise remaining tensor-unit-factorization input, every unit
of the actual algebraic fiber is a scalar unit times the specialization of a
regular functional unit satisfying a first-order base-coefficient equation. -/
theorem constructedPV_fiber_unit_lift
    (hfactor : ∀ w:(H ⊗[k] H)ˣ, ∃ a b:H, (w:H ⊗[k] H)=a ⊗ₜ[k] b)
    (u:(k ⊗[B] R)ˣ) :
    ∃ χ:Hˣ, ∃ v:Rˣ, ∃ b:B, ∃ a:kˣ,
      Δ (χ:H)=(χ:H) ⊗ₜ[k] (χ:H) ∧
      ρ (v:R)=(v:R) ⊗ₜ[k] (χ:H) ∧
      d (v:R)=algebraMap B R b * (v:R) ∧
      u = Units.map (algebraMap k (k ⊗[B] R)).toMonoidHom a *
        Units.map (algebraicFiberSpecialization (k:=k) (B:=B) (R:=R)).toMonoidHom v := by
  letI := pvConstantBialgebra dB d hb he hc
  have hco : ∀ r:R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((ρ).restrictScalars k) (AlgHom.id k H) (ρ r)) =
      weightBaseChangeAlgHom (B := k) (R := H) (T := H ⊗[k] H) R
        (Bialgebra.comulAlgHom k H) (ρ r) := by
    intro r
    exact inverseMultiplicationCoaction_coassoc dB d hb he hc r
  exact fiber_unit_lift_from_character_lifts d e hco
    (constructedPV_character_unit_equation dB d hb he hc) hfactor u
end StrictEUnit
#print axioms StrictEUnit.constructedPV_fiber_unit_lift
