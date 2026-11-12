import CandidateCoaction

/-! Actual counit obtained by tensor multiplication and the exact constant field.
This supplies counitality only, not comultiplication or coassociativity. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped TensorProduct
namespace StrictEUnit
variable {k B R : Type*} [Field k] [CommRing B] [CommRing R] [Nontrivial R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

def diagonalTensorMul : R ⊗[B] R →ₐ[B] R :=
  Algebra.TensorProduct.lift (AlgHom.id B R) (AlgHom.id B R) (fun _ _ => Commute.all _ _)

@[simp] theorem diagonalTensorMul_tmul (r s : R) :
    diagonalTensorMul (B := B) (r ⊗ₜ[B] s) = r*s := rfl

theorem diagonalTensorMul_differential
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) (z : R ⊗[B] R) :
    d (diagonalTensorMul z) = diagonalTensorMul (relativeTensorDerivation dB d hb z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul r s =>
    simp only [diagonalTensorMul_tmul, relativeTensorDerivation_tmul, map_add,
      Derivation.leibniz, smul_eq_mul]
    simp only [mul_comm, add_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

def scalarConstantsEquiv (d : Derivation k R R)
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) :
    k ≃ₐ[k] derivationConstants d :=
  AlgEquiv.ofBijective ((Algebra.ofId k R).codRestrict (derivationConstants d)
    (fun c => d.map_algebraMap c)) ⟨by
      intro a b hab
      exact (algebraMap k R).injective (congrArg Subtype.val hab), by
      intro x
      obtain ⟨c,hc⟩ := hc x x.property
      exact ⟨c,Subtype.ext hc⟩⟩

@[simp] theorem scalarConstantsEquiv_coe (d : Derivation k R R)
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) (c:k) :
    (scalarConstantsEquiv d hc c : R) = algebraMap k R c := rfl

def diagonalConstantsToConstants
    (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) :
    pvConstantAlgebra dB d hb →ₐ[k] derivationConstants d :=
  (((diagonalTensorMul (B := B) (R := R)).restrictScalars k).comp
    (pvConstantAlgebra dB d hb).val).codRestrict (derivationConstants d) (by
      intro h
      change d (diagonalTensorMul (h : R ⊗[B] R)) = 0
      rw [diagonalTensorMul_differential dB d hb, h.property, map_zero])

def candidateCounit (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) :
    pvConstantAlgebra dB d hb →ₐ[k] k :=
  (scalarConstantsEquiv d hc).symm.toAlgHom.comp (diagonalConstantsToConstants dB d hb)

theorem candidateCounit_scalar (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (h : pvConstantAlgebra dB d hb) :
    algebraMap k R (candidateCounit dB d hb hc h) = diagonalTensorMul (h : R ⊗[B] R) := by
  exact congrArg Subtype.val ((scalarConstantsEquiv d hc).apply_symm_apply
    (diagonalConstantsToConstants dB d hb h))

def candidateCounitEval (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r) :
    R ⊗[k] pvConstantAlgebra dB d hb →ₐ[k] R :=
  Algebra.TensorProduct.lift (AlgHom.id k R)
    ((Algebra.ofId k R).comp (candidateCounit dB d hb hc)) (fun _ _ => Commute.all _ _)

theorem candidateCounitEval_eq_mul (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (z : R ⊗[k] pvConstantAlgebra dB d hb) :
    candidateCounitEval dB d hb hc z = diagonalTensorMul (pvConstantMultiplication dB d hb z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
    have he0 : candidateCounitEval dB d hb hc
        (0 : R ⊗[k] pvConstantAlgebra dB d hb) = 0 :=
      (candidateCounitEval dB d hb hc).map_zero'
    have hp0 : pvConstantMultiplication dB d hb
        (0 : R ⊗[k] pvConstantAlgebra dB d hb) = 0 :=
      (pvConstantMultiplication dB d hb).map_zero'
    have hd0 : diagonalTensorMul (0 : R ⊗[B] R) = 0 :=
      (diagonalTensorMul (B := B) (R := R)).map_zero'
    simp only [he0, hp0, hd0]
  | tmul r h =>
    change r * algebraMap k R (candidateCounit dB d hb hc h) = _
    rw [candidateCounit_scalar, pvConstantMultiplication_tmul, map_mul, diagonalTensorMul_tmul, mul_one]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem candidateCounit_identity (dB : Derivation k B B) (d : Derivation k R R)
    (hb : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (hc : ∀ r, d r = 0 → ∃ c:k, algebraMap k R c = r)
    (he : Function.Bijective (pvConstantMultiplication dB d hb)) (r : R) :
    candidateCounitEval dB d hb hc
      (inverseMultiplicationCoaction (AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he) r) = r := by
  rw [candidateCounitEval_eq_mul, inverseMultiplicationCoaction_apply]
  change diagonalTensorMul ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he)
    ((AlgEquiv.ofBijective (pvConstantMultiplication dB d hb) he).symm ((1:R) ⊗ₜ[B] r))) = r
  rw [AlgEquiv.apply_symm_apply, diagonalTensorMul_tmul, one_mul]

section ActualCandidate
variable {L n : Type*} [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Fintype n] [DecidableEq n]

theorem candidateKDerivation_constants
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
    (r : matrixGeneratedAlgebra (B := B) Y)
    (hr : candidateKDerivation dB dL Y A hb hy r = 0) :
    ∃ c:k, algebraMap k (matrixGeneratedAlgebra (B := B) Y) c = r := by
  have hrL : dL (r:L) = 0 := congrArg Subtype.val hr
  obtain ⟨c,hc⟩ := hc r hrL
  exact ⟨c,Subtype.ext hc⟩

def actualCandidateCounit
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B)
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a) :=
  candidateCounit dB (candidateKDerivation dB dL Y A hb hy)
    (candidateKDerivation_base dB dL Y A hb hy)
    (candidateKDerivation_constants dB dL Y A hb hy hc)

theorem actualCandidateCounit_identity
    (dB : Derivation k B B) (dL : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    [Module.Flat B (matrixGeneratedAlgebra (B := B) Y)]
    (hb : ∀ b, dL (algebraMap B L b) = algebraMap B L (dB b))
    (hy : ∀ i j, dL (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hc : ∀ a, dL a = 0 → ∃ c:k, algebraMap k L c = a)
    (r : matrixGeneratedAlgebra (B := B) Y) :
    candidateCounitEval dB (candidateKDerivation dB dL Y A hb hy)
      (candidateKDerivation_base dB dL Y A hb hy)
      (candidateKDerivation_constants dB dL Y A hb hy hc)
      (actualCandidateCoaction dB dL Y A hdet hb hy hc r) = r :=
  candidateCounit_identity _ _ _ _
    (candidateConstantMultiplication_bijective dB dL Y A hdet hb hy hc) r
end ActualCandidate

#print axioms diagonalTensorMul
#print axioms diagonalTensorMul_tmul
#print axioms diagonalTensorMul_differential
#print axioms scalarConstantsEquiv
#print axioms scalarConstantsEquiv_coe
#print axioms diagonalConstantsToConstants
#print axioms candidateCounit
#print axioms candidateCounit_scalar
#print axioms candidateCounitEval
#print axioms candidateCounitEval_eq_mul
#print axioms candidateCounit_identity
#print axioms candidateKDerivation_constants
#print axioms actualCandidateCounit
#print axioms actualCandidateCounit_identity
end StrictEUnit
