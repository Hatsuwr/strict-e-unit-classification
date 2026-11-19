import DifferentialPresentationRank
import MatrixCokernelLocalization

/-! Projectivity of finite differential modules over a nontrivial Noetherian
differentially simple ring. Presentation, constant rank, local freeness,
and localization compatibility are proved, not supplied as premises. -/
noncomputable section
namespace StrictEUnit
variable {B : Type*} [CommRing B] [IsNoetherianRing B]
variable {n m : Type*} [Fintype n] [Fintype m]

theorem matrixCokernel_projective_global (A : Matrix n m B) (r:ℕ)
    (ht:matrixMinorIdeal r A=⊤) (hz:matrixMinorIdeal (r+1) A=⊥) :
    Module.Projective B ((n→B) ⧸ LinearMap.range A.mulVecLin) := by
  letI := Module.finitePresentation_of_finite B ((n→B) ⧸ LinearMap.range A.mulVecLin)
  apply Module.projective_of_localization_maximal'
    (fun I _ => Localization.AtPrime I)
    (fun I _ => matrixLocalizedCokernel (Localization.AtPrime I) I.primeCompl A)
    (fun I _ => matrixCokernelLocalizationMap (Localization.AtPrime I) I.primeCompl A)
  intro I hI
  exact matrixLocalizedCokernel_projective (Localization.AtPrime I) I.primeCompl A r ht hz

variable {k M : Type*} [CommRing k] [Algebra k B] [Nontrivial B]
  [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M] [Module.Finite B M]

theorem finite_differential_module_projective
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x)
    (hsimple : ∀ I : Ideal B, (∀ x ∈ I, δ x ∈ I) → I ≠ ⊥ → I = ⊤) :
    Module.Projective B M := by
  obtain ⟨n,m,A,⟨e⟩,hd,r,hr,ht,hz⟩ :=
    finite_differential_matrix_cokernel_rank δ D hD hsimple
  letI := matrixCokernel_projective_global A r ht hz
  exact Module.Projective.of_equiv e

#print axioms matrixCokernel_projective_global
#print axioms finite_differential_module_projective
end StrictEUnit
