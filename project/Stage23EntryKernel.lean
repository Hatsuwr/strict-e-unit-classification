import Stage23ActualPolynomialLifts
import Stage23EntryAlgebraPresentation

/-! Exact kernel on the actual pre-determinant-localization frame algebra.
The global analytic lifting premise is transferred to genuine Taylor entries;
no kernel or fiber-injectivity premise is introduced. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] formalAmbientBaseAlgebra
attribute [local instance 2000] formalAmbientBaseTower
attribute [local instance 10] laurentLogPointAlgebra laurentLogPointTower

section Generic
variable {k L K : Type*} [Field k] [Field L] [CommRing K]
    [Algebra k L] [Algebra k K] [Algebra (LaurentLogBase k) L]
    [IsScalarTower k (LaurentLogBase k) L]
    {n : Type*}

/-- Ambient polynomial relations descend to the actual entry subalgebra by
its literal inclusion, whose injectivity is automatic. -/
theorem stage23_entry_polynomial_lifts (Y : Matrix n n L) (N : ℕ)
    (ev : matrixEntryAlgebra (B:=LaurentLogBase k) Y →ₐ[k] K)
    (hlift : ∀ P : MvPolynomial (n × n) k,
      ev (MvPolynomial.aeval (stage23_entry (k:=k) Y) P) = 0 →
      ∃ Q : Polynomial (MvPolynomial (n × n) k),
        Polynomial.eval₂ (MvPolynomial.aeval (fun ij : n × n => Y ij.1 ij.2)).toRingHom
          ((algebraMap (LaurentLogBase k) L (Polynomial.C (LaurentPolynomial.T 1)))^N) Q = 0 ∧
        Q.eval 1 = P)
    (P : MvPolynomial (n × n) k)
    (hP : ev (MvPolynomial.aeval (stage23_entry (k:=k) Y) P) = 0) :
    ∃ Q : Polynomial (MvPolynomial (n × n) k),
      Polynomial.eval₂ (MvPolynomial.aeval (stage23_entry (k:=k) Y)).toRingHom
        ((manuscriptParameterUnit (k:=k)
          (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y) :
          matrixEntryAlgebra (B:=LaurentLogBase k) Y)^N) Q = 0 ∧ Q.eval 1 = P := by
  obtain ⟨Q, hQ, hQP⟩ := hlift P hP
  refine ⟨Q, ?_, hQP⟩
  apply Subtype.val_injective
  let φ := (matrixEntryAlgebra (B:=LaurentLogBase k) Y).val.restrictScalars k
  have h := stage23_map_polynomial_mv_eval φ (stage23_entry (k:=k) Y)
    ((manuscriptParameterUnit (k:=k)
      (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y) :
      matrixEntryAlgebra (B:=LaurentLogBase k) Y)^N) Q
  exact h.trans hQ

/-- The exact entry-algebra kernel follows from actual generation and actual
ambient Q-relations. This is the pre-localization input to the fiber theorem. -/
theorem stage23_entry_exact_kernel (Y : Matrix n n L) (N : ℕ)
    (ev : matrixEntryAlgebra (B:=LaurentLogBase k) Y →ₐ[k] K)
    (ht : ev (manuscriptParameterUnit (k:=k)
      (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y) :
      matrixEntryAlgebra (B:=LaurentLogBase k) Y) = 1)
    (hl : ev (manuscriptLogParameter (k:=k)
      (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y)) = 0)
    (hlift : ∀ P : MvPolynomial (n × n) k,
      ev (MvPolynomial.aeval (stage23_entry (k:=k) Y) P) = 0 →
      ∃ Q : Polynomial (MvPolynomial (n × n) k),
        Polynomial.eval₂ (MvPolynomial.aeval (fun ij : n × n => Y ij.1 ij.2)).toRingHom
          ((algebraMap (LaurentLogBase k) L (Polynomial.C (LaurentPolynomial.T 1)))^N) Q = 0 ∧
        Q.eval 1 = P) :
    RingHom.ker ev.toRingHom =
      Ideal.map (algebraMap (LaurentLogBase k) (matrixEntryAlgebra (B:=LaurentLogBase k) Y))
        (RingHom.ker (algebraMap (LaurentLogBase k) k)) :=
  manuscript_exact_kernel_of_polynomial_lifts ev (stage23_entry (k:=k) Y) N
    (stage23_entry_algebra_generated Y) ht hl (stage23_entry_polynomial_lifts Y N ev hlift)
end Generic

section Actual
local notation "k₀" => IntermediateField.toSubfield (algebraicClosure ℚ ℂ)
variable (hBeukers : StrictELaurentRelationLifting)
    {n : Type} [Fintype n] [DecidableEq n]
    (N : ℕ) (hN : N ≠ 0)
    (B : Matrix n n (LaurentPolynomial k₀))
    (M : Matrix n n k₀) (F : Matrix n n (subfieldEntireFunctionAlgebra k₀))
    (hstrict : ∀ i j, IsStrictEFunction (F i j).val.val)
    (hF : Stage17ActualEulerFrameRelation k₀ B M F)
local notation "Y" => stage17_formalFrame k₀ N hN F
local notation "EntryRing" => matrixEntryAlgebra (B:=LaurentLogBase k₀) Y
include hBeukers B M hstrict hF

/-- A numerical relation under any entry-compatible evaluation on this actual
frame has the genuine Q-lift supplied conditionally by the published input. -/
theorem stage23_actual_entry_lifts (ev : EntryRing →ₐ[k₀] ℂ)
    (he : ∀ ij : n × n, ev (stage23_entry (k:=k₀) Y ij) = (F ij.1 ij.2).val.val 1)
    (P : MvPolynomial (n × n) k₀)
    (hP : ev (MvPolynomial.aeval (stage23_entry (k:=k₀) Y) P) = 0) :
    ∃ Q : Polynomial (MvPolynomial (n × n) k₀),
      Polynomial.eval₂ (MvPolynomial.aeval (R:=k₀) (fun ij : n × n => Y ij.1 ij.2)).toRingHom
        (formalBaseEmbedding (Polynomial.C (LaurentPolynomial.T 1)) ^ N) Q = 0 ∧
      Q.eval 1 = P := by
  have hp := (MvPolynomial.comp_aeval_apply (stage23_entry (k:=k₀) Y) ev P).symm.trans hP
  simp only [he] at hp
  exact stage23_arithmeticEulerFrame_formal_polynomial_lifts hBeukers N hN B M F hstrict hF P hp

/-- The exact kernel on the actual frame's entry algebra, conditional only on
the explicit lifting input and the stated generator evaluations. -/
theorem stage23_actual_entry_exact_kernel (ev : EntryRing →ₐ[k₀] ℂ)
    (he : ∀ ij : n × n, ev (stage23_entry (k:=k₀) Y ij) = (F ij.1 ij.2).val.val 1)
    (ht : ev (manuscriptParameterUnit (k:=k₀) (R:=EntryRing) : EntryRing) = 1)
    (hl : ev (manuscriptLogParameter (k:=k₀) (R:=EntryRing)) = 0) :
    RingHom.ker ev.toRingHom = Ideal.map (algebraMap (LaurentLogBase k₀) EntryRing)
      (RingHom.ker (algebraMap (LaurentLogBase k₀) k₀)) := by
  apply stage23_entry_exact_kernel Y N ev ht hl
  exact stage23_actual_entry_lifts hBeukers N hN B M F hstrict hF ev he
end Actual
end StrictEUnit
