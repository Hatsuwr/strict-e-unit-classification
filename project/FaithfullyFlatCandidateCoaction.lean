import CandidateFaithfullyFlat
import CandidateDifferentialCoaction
import CandidateCounit

/-! Actual candidate multiplication, coaction, differential compatibility and
counitality with faithful flatness proved rather than assumed. An ambient
constant field and an invertible fundamental solution matrix remain inputs.
No bialgebra or coassociativity is asserted by this module. -/
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
section General
variable {k B L n : Type*} [Field k] [CommRing B] [IsNoetherianRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]
variable (dB : Derivation k B B) (dL : Derivation k L L)
  (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
  (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
  (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
  (hsimple : ∀ I : Ideal B, (∀ x ∈ I, dB x ∈ I) → I ≠ ⊥ → I = ⊤)
  (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
include hdet hsimple hc in
theorem faithfullyFlatCandidateMultiplication_bijective :
    Function.Bijective (pvConstantMultiplication dB
      (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy)) := by
  letI := matrixGeneratedAlgebra_faithfullyFlat dB dL Y A hdet hb hy hsimple
  exact candidateConstantMultiplication_bijective dB dL Y A hdet hb hy hc

def faithfullyFlatCandidateMultiplicationEquiv :=
  AlgEquiv.ofBijective (pvConstantMultiplication dB
    (candidateKDerivation dB dL Y A hb hy) (candidateKDerivation_base dB dL Y A hb hy))
    (faithfullyFlatCandidateMultiplication_bijective dB dL Y A hdet hb hy hsimple hc)

def faithfullyFlatCandidateCoaction :=
  inverseMultiplicationCoaction
    (faithfullyFlatCandidateMultiplicationEquiv dB dL Y A hdet hb hy hsimple hc)

theorem faithfullyFlatCandidateCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical
      (faithfullyFlatCandidateCoaction dB dL Y A hdet hb hy hsimple hc)) :=
  relativeCandidateCanonical_bijective _

theorem faithfullyFlatCandidateCoaction_differential
    (r : matrixGeneratedAlgebra (B := B) Y) :
    tensorDerivation (candidateKDerivation dB dL Y A hb hy)
      (faithfullyFlatCandidateCoaction dB dL Y A hdet hb hy hsimple hc r) =
      faithfullyFlatCandidateCoaction dB dL Y A hdet hb hy hsimple hc
        (candidateKDerivation dB dL Y A hb hy r) :=
  inverseMultiplicationCoaction_differential _ _ _
    (faithfullyFlatCandidateMultiplication_bijective dB dL Y A hdet hb hy hsimple hc) r

theorem faithfullyFlatCandidateCoaction_counit
    (r : matrixGeneratedAlgebra (B := B) Y) :
    candidateCounitEval dB (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy)
      (candidateKDerivation_constants dB dL Y A hb hy hc)
      (faithfullyFlatCandidateCoaction dB dL Y A hdet hb hy hsimple hc r) = r :=
  candidateCounit_identity _ _ _ _
    (faithfullyFlatCandidateMultiplication_bijective dB dL Y A hdet hb hy hsimple hc) r
end General

section Manuscript
variable {k L n : Type*} [Field k] [CharZero k] [Field L]
  [Algebra k L] [Algebra (LaurentLogBase k) L] [IsScalarTower k (LaurentLogBase k) L]
  [Fintype n] [DecidableEq n]
variable (N:ℕ) (hN:N≠0) (dL : Derivation k L L)
  (Y : Matrix n n L) (A : Matrix n n (LaurentLogBase k)) (hdet : Y.det ≠ 0)
  (hb : ∀ b, dL (algebraMap (LaurentLogBase k) L b) =
    algebraMap (LaurentLogBase k) L (manuscriptBaseDerivation (k := k) N b))
  (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap (LaurentLogBase k) L (A i l) * Y l j)
  (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
include hN hdet hc in
theorem manuscriptCandidateMultiplication_bijective :
    Function.Bijective (pvConstantMultiplication (R := (matrixGeneratedAlgebra (B := LaurentLogBase k) Y)) (manuscriptBaseDerivation (k := k) N)
      (candidateKDerivation (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy)
      (candidateKDerivation_base (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy)) := by
  letI := laurentLogBase_isNoetherianRing k
  exact faithfullyFlatCandidateMultiplication_bijective
    (manuscriptBaseDerivation (k := k) N) dL Y A hdet hb hy
    (manuscriptBase_stable_ideal_eq_top N hN) hc

def manuscriptCandidateMultiplicationEquiv :=
  letI := laurentLogBase_isNoetherianRing k
  faithfullyFlatCandidateMultiplicationEquiv
    (manuscriptBaseDerivation (k := k) N) dL Y A hdet hb hy
    (manuscriptBase_stable_ideal_eq_top N hN) hc

def manuscriptCandidateCoaction :=
  letI := laurentLogBase_isNoetherianRing k
  faithfullyFlatCandidateCoaction
    (manuscriptBaseDerivation (k := k) N) dL Y A hdet hb hy
    (manuscriptBase_stable_ideal_eq_top N hN) hc

theorem manuscriptCandidateCoaction_canonical_bijective :
    Function.Bijective (relativeCandidateCanonical
      (manuscriptCandidateCoaction N hN dL Y A hdet hb hy hc)) :=
  relativeCandidateCanonical_bijective _

theorem manuscriptCandidateCoaction_differential
    (r : matrixGeneratedAlgebra (B := LaurentLogBase k) Y) :
    tensorDerivation (R := (matrixGeneratedAlgebra (B := LaurentLogBase k) Y)) (candidateKDerivation (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy)
      (manuscriptCandidateCoaction N hN dL Y A hdet hb hy hc r) =
      manuscriptCandidateCoaction N hN dL Y A hdet hb hy hc
        (candidateKDerivation (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy r) :=
  inverseMultiplicationCoaction_differential _ _ _
    (manuscriptCandidateMultiplication_bijective N hN dL Y A hdet hb hy hc) r

theorem manuscriptCandidateCoaction_counit
    (r : matrixGeneratedAlgebra (B := LaurentLogBase k) Y) :
    candidateCounitEval (R := (matrixGeneratedAlgebra (B := LaurentLogBase k) Y)) (manuscriptBaseDerivation (k := k) N)
      (candidateKDerivation (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy)
      (candidateKDerivation_base (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy)
      (candidateKDerivation_constants (B := LaurentLogBase k) (manuscriptBaseDerivation (k := k) N) dL Y A hb hy hc)
      (manuscriptCandidateCoaction N hN dL Y A hdet hb hy hc r) = r :=
  candidateCounit_identity _ _ _ _
    (manuscriptCandidateMultiplication_bijective N hN dL Y A hdet hb hy hc) r
end Manuscript

#print axioms faithfullyFlatCandidateMultiplication_bijective
#print axioms faithfullyFlatCandidateMultiplicationEquiv
#print axioms faithfullyFlatCandidateCoaction
#print axioms faithfullyFlatCandidateCoaction_canonical_bijective
#print axioms faithfullyFlatCandidateCoaction_differential
#print axioms faithfullyFlatCandidateCoaction_counit
#print axioms manuscriptCandidateMultiplication_bijective
#print axioms manuscriptCandidateMultiplicationEquiv
#print axioms manuscriptCandidateCoaction
#print axioms manuscriptCandidateCoaction_canonical_bijective
#print axioms manuscriptCandidateCoaction_differential
#print axioms manuscriptCandidateCoaction_counit
end StrictEUnit
