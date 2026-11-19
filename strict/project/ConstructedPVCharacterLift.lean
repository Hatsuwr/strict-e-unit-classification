import PVConstantBialgebra
import CandidateActionCoassociativity
import MixedCoactionLaws
import CanonicalDifferentialCharacter
import FaithfullyFlatCandidateCoaction

/-! Character lifting for the actual constructed diagonal-constant bialgebra
and actual inverse-multiplication coaction. All action/canonical/differential
laws are derived. A grouplike character itself remains an explicit input. -/
open scoped TensorProduct
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
section Generic
variable {k B R : Type*} [Field k] [CommRing B] [IsDomain B]
  [UniqueFactorizationMonoid B] [CommRing R] [IsDomain R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Module.FaithfullyFlat B R]
variable (dB : Derivation k B B) (d : Derivation k R R)
  (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
  (he : Function.Bijective (pvConstantMultiplication dB d hb))
  (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
local notation "H" => pvConstantAlgebra dB d hb
local notation "e" => AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he
local notation "ρ" => inverseMultiplicationCoaction e
local notation "Δ" => pvConstantComultiplication dB d hb he hc

/-- A character of the constructed constants bialgebra lifts to a regular unit
and an actual first-order differential equation over the base. -/
theorem constructedPV_character_unit_equation (χ : Hˣ)
    (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ v : Rˣ, ∃ b : B, ρ (v : R) = (v : R) ⊗ₜ[k] (χ : H) ∧
      d (v : R) = algebraMap B R b * (v : R) := by
  letI := pvConstantBialgebra dB d hb he hc
  have hco : ∀ r : R, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map ((ρ).restrictScalars k) (AlgHom.id k H) (ρ r)) =
      weightBaseChangeAlgHom (B := k) (R := H) (T := H ⊗[k] H) R
        (Bialgebra.comulAlgHom k H) (ρ r) := by
    intro r
    exact inverseMultiplicationCoaction_coassoc dB d hb he hc r
  have hd : ∀ r, constantFieldCoaction (scalarTargetCoaction ρ) (d r) =
      tensorDerivation d (constantFieldCoaction (scalarTargetCoaction ρ) r) := by
    intro r
    simp only [constantFieldCoaction_scalarTarget]
    exact (inverseMultiplicationCoaction_differential dB d hb he r).symm
  obtain ⟨v,b,hv,hdb⟩ := exists_character_unit_first_order_equation
    (scalarTargetCoaction ρ)
    (scalarTargetCoaction_canonical_bijective ρ (relativeCandidateCanonical_bijective e))
    (scalarTargetCoaction_coassoc ρ hco) d hd χ hχ
  exact ⟨v,b,(scalarTargetCoaction_weight_iff ρ (v:R) (χ:H)).mp hv,hdb⟩
end Generic

section Candidate
variable {k B L n : Type*} [Field k] [CommRing B] [IsDomain B]
  [UniqueFactorizationMonoid B] [IsNoetherianRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]
variable (dB : Derivation k B B) (dL : Derivation k L L)
  (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
  (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
  (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
  (hsimple : ∀ I : Ideal B, (∀ x ∈ I, dB x ∈ I) → I ≠ ⊥ → I = ⊤)
  (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
local notation "R" => matrixGeneratedAlgebra (B := B) Y
local notation "d" => candidateKDerivation dB dL Y A hb hy
local notation "hd" => candidateKDerivation_base dB dL Y A hb hy
local notation "H" => pvConstantAlgebra dB d hd
local notation "he" => faithfullyFlatCandidateMultiplication_bijective dB dL Y A hdet hb hy hsimple hc
local notation "ρ" => faithfullyFlatCandidateCoaction dB dL Y A hdet hb hy hsimple hc
local notation "Δ" => pvConstantComultiplication dB d hd he
  (candidateKDerivation_constants dB dL Y A hb hy hc)

/-- The genuine matrix-generated candidate meets all structural inputs to the
regular-character lift. Existence of χ and its numerical interpretation remain open inputs. -/
theorem candidate_character_unit_equation (χ : Hˣ)
    (hχ : Δ (χ : H) = (χ : H) ⊗ₜ[k] (χ : H)) :
    ∃ v : Rˣ, ∃ b : B, ρ (v : R) = (v : R) ⊗ₜ[k] (χ : H) ∧
      d (v : R) = algebraMap B R b * (v : R) := by
  letI := matrixGeneratedAlgebra_faithfullyFlat dB dL Y A hdet hb hy hsimple
  exact constructedPV_character_unit_equation dB d hd he
    (candidateKDerivation_constants dB dL Y A hb hy hc) χ hχ
end Candidate
end StrictEUnit
#print axioms StrictEUnit.constructedPV_character_unit_equation

#print axioms StrictEUnit.candidate_character_unit_equation
