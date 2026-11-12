import CandidateCoaction

/-! Differential compatibility is proved for actual constant multiplication,
its inverse, and the resulting candidate coaction; none is an extra premise. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit
section General
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

theorem pvConstantMultiplication_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (z : R ⊗[k] pvConstantAlgebra dB d hb) :
    relativeTensorDerivation dB d hb (pvConstantMultiplication dB d hb z) =
      pvConstantMultiplication dB d hb (tensorDerivation d z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    have hzero : pvConstantMultiplication dB d hb
        (0 : R ⊗[k] pvConstantAlgebra dB d hb) = 0 :=
      (pvConstantMultiplication dB d hb).map_zero'
    simp only [hzero, map_zero (relativeTensorDerivation dB d hb),
      map_zero (tensorDerivation d)]
  | tmul r h =>
    rw [pvConstantMultiplication_tmul, Derivation.leibniz,
      show relativeTensorDerivation dB d hb (h : R ⊗[B] R) = 0 from h.property,
      smul_zero, zero_add, relativeTensorDerivation_tmul,
      d.map_one_eq_zero, TensorProduct.tmul_zero, add_zero,
      tensorDerivation_tmul, pvConstantMultiplication_tmul]
    exact mul_comm _ _
  | add x y hx hy => simp only [map_add, hx, hy]

theorem pvConstantMultiplication_inverse_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb)) (z : R ⊗[B] R) :
    tensorDerivation d ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).symm z) =
      (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).symm
        (relativeTensorDerivation dB d hb z) := by
  apply he.injective
  rw [← pvConstantMultiplication_differential]
  exact congrArg (relativeTensorDerivation dB d hb)
    ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).apply_symm_apply z) |>.trans
      ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).apply_symm_apply _).symm

theorem inverseMultiplicationCoaction_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (he : Function.Bijective (pvConstantMultiplication dB d hb)) (r : R) :
    tensorDerivation d (inverseMultiplicationCoaction
      (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he) r) =
      inverseMultiplicationCoaction
        (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he) (d r) := by
  rw [inverseMultiplicationCoaction_apply, pvConstantMultiplication_inverse_differential,
    relativeTensorDerivation_tmul, d.map_one_eq_zero, TensorProduct.zero_tmul, zero_add,
    inverseMultiplicationCoaction_apply]
end General

section ActualCandidate
variable {k B L n : Type*} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]

theorem actualCandidateCoaction_differential
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c : k, algebraMap k L c = a)
    (r : matrixGeneratedAlgebra (B := B) Y) :
    tensorDerivation (candidateKDerivation dB dL Y A hb hy)
      (actualCandidateCoaction dB dL Y A hdet hb hy hc r) =
      actualCandidateCoaction dB dL Y A hdet hb hy hc
        (candidateKDerivation dB dL Y A hb hy r) :=
  inverseMultiplicationCoaction_differential _ _ _
    (candidateConstantMultiplication_bijective dB dL Y A hdet hb hy hc) r
end ActualCandidate

#print axioms pvConstantMultiplication_differential
#print axioms pvConstantMultiplication_inverse_differential
#print axioms inverseMultiplicationCoaction_differential
#print axioms actualCandidateCoaction_differential
end StrictEUnit
