import V5ExplicitRelativeAssembly134
import V5HopfFixedCoordinates134
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
universe u v t
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k : Type t} {B : Type v} {R H : Type u}
  [Field k] [IsAlgClosed k] [CommRing B] [CommRing R] [CommRing H]
  [HopfAlgebra k H] [Algebra.FiniteType k H] [IsReduced H]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
def v5HopfRelativeAssembly134 [Module.FaithfullyFlat B R]
    (e : R ⊗[k] H ≃ₐ[R] R ⊗[B] R)
    (ρ : R →ₐ[B] R ⊗[k] H)
    (he : ∀ r s, e.symm (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) (Bialgebra.comulAlgHom k H) (ρ r))
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
    (I : Ideal H) (hmin : I ∈ minimalPrimes H)
    (hI : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom)
    (hu : ∀ P ∈ minimalPrimes H,
      P ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → P = I) := by
  classical
  letI := Algebra.FiniteType.isNoetherianRing k H
  letI := (minimalPrimes.finite_of_isNoetherianRing H).to_subtype
  letI : Fintype (minimalPrimes H) := Fintype.ofFinite _
  letI : I.IsPrime := Ideal.minimalPrimes_isPrime hmin
  exact v5ExplicitRelativeAssembly134 e I ρ (Bialgebra.comulAlgHom k H) he hρ
    (v5HopfCanonicalComponentFixedEquiv s hs I hu inferInstance hI)
    (v5HopfComponentRegularProduct s hs I hu)
    (v5HopfCanonicalFixedCoordinates134 s hs I hu inferInstance hI)
    (v5ComponentCounit I (Bialgebra.counitAlgHom k H) hI)
    (⟨I, hmin⟩ : minimalPrimes H)
    (v5HopfAllComponentEquiv s hs I hu (⟨I, hmin⟩ : minimalPrimes H)).toAlgHom
    (fun _ => rfl)
end StrictEUnit
#print axioms StrictEUnit.v5HopfRelativeAssembly134
