import MatrixCandidateTorsorCriterion

/-! Candidate coaction and actual relative canonical equivalence constructed
from constant multiplication. No bialgebra or coassociativity is asserted. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
section General
variable {k B R H : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing H]
  [Algebra k B] [Algebra k R] [Algebra k H] [Algebra B R] [IsScalarTower k B R]

def inverseMultiplicationCoaction (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    R →ₐ[B] R ⊗[k] H :=
  (e.symm.toAlgHom.restrictScalars B).comp Algebra.TensorProduct.includeRight

@[simp] theorem inverseMultiplicationCoaction_apply
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) (r : R) :
    inverseMultiplicationCoaction e r = e.symm ((1:R) ⊗ₜ[B] r) := rfl

/-- The relative canonical map is built by the tensor universal property. -/
def relativeCandidateCanonical (ρ : R →ₐ[B] R ⊗[k] H) :
    R ⊗[B] R →ₐ[B] R ⊗[k] H :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom B R (R ⊗[k] H)) ρ
    (fun _ _ => Commute.all _ _)

@[simp] theorem relativeCandidateCanonical_tmul
    (ρ : R →ₐ[B] R ⊗[k] H) (r s : R) :
    relativeCandidateCanonical ρ (r ⊗ₜ[B] s) =
      (r ⊗ₜ[k] (1:H)) * ρ s := rfl

theorem relativeCandidateCanonical_eq_inverse
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    relativeCandidateCanonical (inverseMultiplicationCoaction e) =
      e.symm.toAlgHom.restrictScalars B := by
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.ext'
  intro r s
  change (r ⊗ₜ[k] (1:H)) * e.symm ((1:R) ⊗ₜ[B] s) = e.symm (r ⊗ₜ[B] s)
  have hr : e.symm (r ⊗ₜ[B] (1:R)) = r ⊗ₜ[k] (1:H) := e.symm.commutes r
  rw [← hr, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem relativeCandidateCanonical_bijective
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R) :
    Function.Bijective (relativeCandidateCanonical (inverseMultiplicationCoaction e)) := by
  rw [relativeCandidateCanonical_eq_inverse]
  exact e.symm.bijective
end General

section ActualCandidate
variable {k B L n : Type*} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]

def actualCandidateCoaction
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a) :=
  inverseMultiplicationCoaction
    (candidateConstantMultiplicationEquiv dB dL Y A hdet hb hy hc)

theorem actualCandidateCoaction_canonical_bijective
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a) :
    Function.Bijective (relativeCandidateCanonical
      (actualCandidateCoaction dB dL Y A hdet hb hy hc)) :=
  relativeCandidateCanonical_bijective _
end ActualCandidate

#print axioms inverseMultiplicationCoaction
#print axioms inverseMultiplicationCoaction_apply
#print axioms relativeCandidateCanonical
#print axioms relativeCandidateCanonical_tmul
#print axioms relativeCandidateCanonical_eq_inverse
#print axioms relativeCandidateCanonical_bijective
#print axioms actualCandidateCoaction
#print axioms actualCandidateCoaction_canonical_bijective
end StrictEUnit
