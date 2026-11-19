import MatrixFiniteDifferentialPieces
import DifferentialQuotientConnection
import FaithfulFlatFromSplitPieces
import Mathlib.RingTheory.Finiteness.Basic
import FiniteDifferentialProjectivity
import NoetherianDifferentialBase
import ManuscriptBaseSimplicity

/-! Faithful-flatness preparation for the actual matrix-generated candidate.
The base inclusion is proved injective from differential simplicity, and the
quotient by its actual image has an actual descended connection. -/
noncomputable section
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [CommRing B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

omit [IsScalarTower k B R] in
/-- Differential simplicity makes every compatible map to a nonzero differential
algebra injective. No domain or field hypothesis on the target is needed. -/
theorem differential_simple_algebraMap_injective [Nontrivial R]
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤) :
    Function.Injective (algebraMap B R) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  by_contra hn
  have htop := hsimple (RingHom.ker (algebraMap B R)) (by
    intro b hb0
    rw [RingHom.mem_ker] at hb0 ⊢
    rw [← hb, hb0, map_zero]) hn
  exact RingHom.ker_ne_top (algebraMap B R) htop

omit [IsScalarTower k B R] in
/-- A compatible algebra derivation obeys the required module-connection law. -/
theorem algebraDerivation_connection_leibniz
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (b : B) (x : R) : D (b • x) = δ b • x + b • D x := by
  simp only [Algebra.smul_def, D.leibniz, smul_eq_mul, hb, Algebra.id.map_eq_self, RingHom.id_apply]
  ring

/-- The actual embedded copy of the base is stable in every stable piece containing 1. -/
theorem submoduleUnitInclusion_range_stable
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (P : Submodule B R) (h1 : (1 : R) ∈ P) (hP : ∀ x ∈ P, D x ∈ P) :
    ∀ x ∈ LinearMap.range (submoduleUnitInclusion P h1),
      restrictConnection P D.toLinearMap hP x ∈ LinearMap.range (submoduleUnitInclusion P h1) := by
  rintro x ⟨b,rfl⟩
  refine ⟨δ b, ?_⟩
  apply Subtype.ext
  exact (hb b).symm

/-- The connection on P/B is constructed by descent through the stable actual image. -/
def unitPieceQuotientConnection
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (P : Submodule B R) (h1 : (1 : R) ∈ P) (hP : ∀ x ∈ P, D x ∈ P) :
    (P ⧸ LinearMap.range (submoduleUnitInclusion P h1)) →ₗ[k]
      (P ⧸ LinearMap.range (submoduleUnitInclusion P h1)) :=
  quotientConnection _ (restrictConnection P D.toLinearMap hP)
    (submoduleUnitInclusion_range_stable δ D hb P h1 hP)

theorem unitPieceQuotientConnection_leibniz
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (P : Submodule B R) (h1 : (1 : R) ∈ P) (hP : ∀ x ∈ P, D x ∈ P)
    (b : B) (x : P ⧸ LinearMap.range (submoduleUnitInclusion P h1)) :
    unitPieceQuotientConnection δ D hb P h1 hP (b • x) =
      δ b • x + b • unitPieceQuotientConnection δ D hb P h1 hP x := by
  exact quotientConnection_leibniz δ _ (restrictConnection P D.toLinearMap hP)
    (submoduleUnitInclusion_range_stable δ D hb P h1 hP)
    (restrictConnection_leibniz δ P D.toLinearMap hP
      (algebraDerivation_connection_leibniz δ D hb)) b x
/-- Actual finite stable pieces over a Noetherian differentially simple base
are faithfully flat in aggregate. Both P and P/B receive proved connections
and are projective by the finite differential-module theorem. -/
theorem faithfullyFlat_of_finite_differential_pieces [IsNoetherianRing B] [Nontrivial R]
    (δ : Derivation k B B) (D : Derivation k R R)
    (hb : ∀ b, D (algebraMap B R b) = algebraMap B R (δ b))
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤)
    (hpieces : ∀ s : Finset R, ∃ P : Submodule B R, P.FG ∧ (1 : R) ∈ P ∧
      (∀ x ∈ P, D x ∈ P) ∧ ∀ x ∈ s, x ∈ P) :
    Module.FaithfullyFlat B R := by
  letI : Nontrivial B := (algebraMap B R).domain_nontrivial
  apply faithfullyFlat_of_projective_pieces_and_quotients
    (differential_simple_algebraMap_injective δ D hb hsimple)
  intro s
  obtain ⟨P,hfg,h1,hP,hs⟩ := hpieces s
  letI : Module.Finite B P := Module.Finite.iff_fg.mpr hfg
  have hp : Module.Projective B P := finite_differential_module_projective δ
    (restrictConnection P D.toLinearMap hP)
    (restrictConnection_leibniz δ P D.toLinearMap hP
      (algebraDerivation_connection_leibniz δ D hb)) hsimple
  have hq : Module.Projective B (P ⧸ LinearMap.range (submoduleUnitInclusion P h1)) :=
    finite_differential_module_projective δ (unitPieceQuotientConnection δ D hb P h1 hP)
      (unitPieceQuotientConnection_leibniz δ D hb P h1 hP) hsimple
  exact ⟨P,hp,h1,hq,hs⟩

/-- A genuine invertible fundamental matrix generates a faithfully flat algebra
over any Noetherian differentially simple base. No faithful-flatness,
injectivity, finite-piece projectivity, or quotient projectivity is assumed. -/
theorem matrixGeneratedAlgebra_faithfullyFlat [IsNoetherianRing B]
    {L n : Type*} [Field L] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
    [Fintype n] [DecidableEq n]
    (δ : Derivation k B B) (D : Derivation k L L)
    (Y : Matrix n n L) (A : Matrix n n B) (hdet : Y.det ≠ 0)
    (hb : ∀ b, D (algebraMap B L b) = algebraMap B L (δ b))
    (hy : ∀ i j, D (Y i j) = ∑ l, algebraMap B L (A i l) * Y l j)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤) :
    Module.FaithfullyFlat B (matrixGeneratedAlgebra (B := B) Y) := by
  classical
  apply faithfullyFlat_of_finite_differential_pieces δ
    (candidateKDerivation δ D Y A hb hy)
    (candidateKDerivation_base δ D Y A hb hy) hsimple
  intro s
  obtain ⟨P,hfg,ht,hP⟩ := candidate_finite_differential_pieces δ D Y A hdet hb hy
    (insert 1 (s : Set (matrixGeneratedAlgebra (B := B) Y))) (s.finite_toSet.insert 1)
  exact ⟨P,hfg,ht (Set.mem_insert _ _),hP,fun x hx => ht (Set.mem_insert_of_mem _ hx)⟩

/-- Specialization to the actual abstract manuscript base k[t,t⁻¹][ell],
D(t)=t/N, D(ell)=1. No Noetherianity or differential-simplicity premise remains. -/
theorem manuscript_matrixGeneratedAlgebra_faithfullyFlat
    {K L n : Type*} [Field K] [CharZero K] [Field L]
    [Algebra K L] [Algebra (LaurentLogBase K) L] [IsScalarTower K (LaurentLogBase K) L]
    [Fintype n] [DecidableEq n]
    (N : ℕ) (hN : N ≠ 0) (D : Derivation K L L)
    (Y : Matrix n n L) (A : Matrix n n (LaurentLogBase K)) (hdet : Y.det ≠ 0)
    (hb : ∀ b, D (algebraMap (LaurentLogBase K) L b) =
      algebraMap (LaurentLogBase K) L (manuscriptBaseDerivation N b))
    (hy : ∀ i j, D (Y i j) = ∑ l, algebraMap (LaurentLogBase K) L (A i l) * Y l j) :
    Module.FaithfullyFlat (LaurentLogBase K)
      (matrixGeneratedAlgebra (B := LaurentLogBase K) Y) := by
  letI := laurentLogBase_isNoetherianRing K
  exact matrixGeneratedAlgebra_faithfullyFlat (manuscriptBaseDerivation N) D Y A hdet hb hy
    (manuscriptBase_stable_ideal_eq_top N hN)

end StrictEUnit
#print axioms StrictEUnit.differential_simple_algebraMap_injective
#print axioms StrictEUnit.algebraDerivation_connection_leibniz
#print axioms StrictEUnit.submoduleUnitInclusion_range_stable
#print axioms StrictEUnit.unitPieceQuotientConnection
#print axioms StrictEUnit.unitPieceQuotientConnection_leibniz
#print axioms StrictEUnit.faithfullyFlat_of_finite_differential_pieces
#print axioms StrictEUnit.matrixGeneratedAlgebra_faithfullyFlat


#print axioms StrictEUnit.manuscript_matrixGeneratedAlgebra_faithfullyFlat
