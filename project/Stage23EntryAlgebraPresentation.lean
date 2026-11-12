import BeukersFiberConsequence
import MatrixGeneratedDifferentialAlgebra

/-! The actual entry algebra over the finite Laurent-log base has precisely
the generators required by the exact-kernel theorem. No presentation equality
or algebraic independence is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit
variable {k R : Type*} [Field k] [CommRing R]
    [Algebra k R] [Algebra (LaurentLogBase k) R]
    [IsScalarTower k (LaurentLogBase k) R]

/-- Constants and the three actual parameters generate the image of the full
finite Laurent-log base. -/
theorem stage23_base_mem_parameter_adjoin (S : Subalgebra k R)
    (ht : (manuscriptParameterUnit (k:=k) (R:=R) : R) ∈ S)
    (hti : (↑((manuscriptParameterUnit (k:=k) (R:=R))⁻¹) : R) ∈ S)
    (hl : manuscriptLogParameter (k:=k) (R:=R) ∈ S)
    (p : LaurentLogBase k) : algebraMap (LaurentLogBase k) R p ∈ S := by
  let φ := algebraMap (LaurentLogBase k) R
  have hC (a : k) : φ (Polynomial.C (LaurentPolynomial.C a)) ∈ S := by
    change algebraMap (LaurentLogBase k) R (algebraMap k (LaurentLogBase k) a) ∈ S
    rw [← IsScalarTower.algebraMap_apply]
    exact S.algebraMap_mem a
  have hT (n : ℤ) : φ (Polynomial.C (LaurentPolynomial.T n)) ∈ S := by
    induction n using Int.induction_on with
    | hz => simpa using S.one_mem
    | hp n ih =>
      rw [LaurentPolynomial.T_add, map_mul, map_mul]
      exact S.mul_mem ih ht
    | hn n ih =>
      rw [sub_eq_add_neg, LaurentPolynomial.T_add, map_mul, map_mul]
      exact S.mul_mem ih hti
  have hLaurent (q : LaurentPolynomial k) : φ (Polynomial.C q) ∈ S := by
    induction q using LaurentPolynomial.induction_on' with
    | add q r hq hr => rw [map_add, map_add]; exact S.add_mem hq hr
    | C_mul_T n a => rw [map_mul, map_mul]; exact S.mul_mem (hC a) (hT n)
  change φ p ∈ S
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact S.add_mem hp hq
  | monomial j a =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact S.mul_mem (hLaurent a) (S.pow_mem hl j)

variable {L : Type*} [Field L] [Algebra k L]
    [Algebra (LaurentLogBase k) L] [IsScalarTower k (LaurentLogBase k) L]
    {n : Type*}

/-- Actual entries as elements of their pre-determinant-localization algebra. -/
def stage23_entry (Y : Matrix n n L) (ij : n × n) :
    matrixEntryAlgebra (B := LaurentLogBase k) Y :=
  ⟨Y ij.1 ij.2, matrixEntry_mem Y ij.1 ij.2⟩

/-- Generation over k is proved for the actual subalgebra generated over
k[t,t⁻¹,ell], with no independence or freeness condition. -/
theorem stage23_entry_algebra_generated (Y : Matrix n n L) :
    Algebra.adjoin k (Set.range (stage23_entry (k:=k) Y) ∪ Set.range
      (laurentLogFiberParameters
        (manuscriptParameterUnit (k:=k) (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y))
        (manuscriptLogParameter (k:=k) (R:=matrixEntryAlgebra (B:=LaurentLogBase k) Y)))) = ⊤ := by
  let R := matrixEntryAlgebra (B:=LaurentLogBase k) Y
  let S : Subalgebra k R := Algebra.adjoin k (Set.range (stage23_entry (k:=k) Y) ∪ Set.range
    (laurentLogFiberParameters (manuscriptParameterUnit (k:=k) (R:=R))
      (manuscriptLogParameter (k:=k) (R:=R))))
  have hb (p : LaurentLogBase k) : algebraMap (LaurentLogBase k) R p ∈ S := by
    refine stage23_base_mem_parameter_adjoin (k:=k) (R:=R) S ?_ ?_ ?_ p
    · exact Algebra.subset_adjoin (Or.inr ⟨none, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨some false, rfl⟩)
    · exact Algebra.subset_adjoin (Or.inr ⟨some true, rfl⟩)
  apply eq_top_iff.mpr
  intro x hx
  change x ∈ S
  have heAll : ∀ (z : L), z ∈ Algebra.adjoin (LaurentLogBase k)
      (Set.range fun ij : n × n => Y ij.1 ij.2) → ∃ y : S, ((y : R) : L) = z := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨ij, rfl⟩ := hz
      exact ⟨⟨stage23_entry (k:=k) Y ij, Algebra.subset_adjoin (Or.inl ⟨ij, rfl⟩)⟩, rfl⟩
    | algebraMap a => exact ⟨⟨algebraMap (LaurentLogBase k) R a, hb a⟩, rfl⟩
    | add a b ha hb iha ihb =>
      obtain ⟨a', rfl⟩ := iha
      obtain ⟨b', rfl⟩ := ihb
      exact ⟨a' + b', rfl⟩
    | mul a b ha hb iha ihb =>
      obtain ⟨a', rfl⟩ := iha
      obtain ⟨b', rfl⟩ := ihb
      exact ⟨a' * b', rfl⟩
  obtain ⟨y, hy⟩ := heAll x x.property
  have hxy : (y : R) = x := Subtype.ext hy
  exact hxy ▸ y.property

end StrictEUnit
