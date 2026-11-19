import V5WideOwnIdentityComponent
import V5PairwiseComponents
import V5MinimalPrimeCRT

noncomputable section
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 30000
namespace StrictEUnit

section Generic
variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H]

theorem v5_hopf_pairwise_minimal_prime
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode) :
    Pairwise (fun P Q : minimalPrimes H => IsCoprime (P : Ideal H) (Q : Ideal H)) := by
  intro P Q hne
  apply Ideal.isCoprime_iff_sup_eq.mpr
  exact v5_minimalPrimes_pairwise_comaximal_of_point_transitive
    (Bialgebra.counitAlgHom k H) (v5_unique_hopf_identityPrime s hs)
    (fun p => ⟨v5HopfTranslation s hs p, v5HopfTranslation_at_counit s hs p⟩)
    P Q P.property Q.property (fun h => hne (Subtype.ext h))

/-- The product decomposition of a reduced finite-type Hopf algebra, indexed
by its minimal primes. Finite index and comaximality follow internally. -/
def v5_hopf_minimalPrimeCRT [IsReduced H]
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode) :
    H ≃ₐ[k] ∀ P : minimalPrimes H, H ⧸ (P : Ideal H) := by
  letI := Algebra.FiniteType.isNoetherianRing k H
  letI := (minimalPrimes.finite_of_isNoetherianRing H).to_subtype
  exact v5MinimalPrimeCRT (v5_hopf_pairwise_minimal_prime s hs)
end Generic

attribute [-instance] TensorProduct.leftModule Polynomial.commSemiring
attribute [-instance] HahnSeries.instModule HahnSeries.instSMul
attribute [local instance 2000] Algebra.toModule
attribute [local instance 4000] Subalgebra.algebra Subalgebra.toCommRing
local instance : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
variable {r : ℕ} (A : Matrix (Fin r) (Fin r) V5LaurentBase)

theorem v5WideOwnPairwiseMinimalPrime :
    Pairwise (fun P Q : minimalPrimes (V5WideOwnConstants A) =>
      IsCoprime (P : Ideal (V5WideOwnConstants A)) (Q : Ideal (V5WideOwnConstants A))) := by
  letI := v5WideOwnHopfAlgebra A
  letI : Algebra.FiniteType AlgebraicComplex (V5WideOwnConstants A) := v5WideOwnConstants_finiteType A
  exact v5_hopf_pairwise_minimal_prime (k := AlgebraicComplex) (v5WideOwnAntipode A) rfl

end StrictEUnit
#print axioms StrictEUnit.v5_hopf_pairwise_minimal_prime
#print axioms StrictEUnit.v5_hopf_minimalPrimeCRT
#print axioms StrictEUnit.v5WideOwnPairwiseMinimalPrime
