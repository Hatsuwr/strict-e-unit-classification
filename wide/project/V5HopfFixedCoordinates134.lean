import V5CanonicalFixedCoordinates132
import V5HopfComponentInvariants
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
  [Algebra.FiniteType k H] [IsReduced H]
theorem v5HopfCanonicalFixedCoordinates134
    (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
    (I : Ideal H)
    (hu : ∀ P ∈ minimalPrimes H,
      P ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → P = I)
    (hprime : I.IsPrime)
    (hI : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom)
    (x : AlgHom.equalizer (v5HopfComponentAction (k := k) I)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] (H ⧸ I)))
    (j : minimalPrimes H) :
    v5HopfComponentRegularProduct s hs I hu x j =
      algebraMap k (H ⧸ I) (v5HopfCanonicalComponentFixedEquiv s hs I hu hprime hI x j) := by
  letI : I.IsPrime := hprime
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  letI := Algebra.FiniteType.isNoetherianRing k H
  letI := (minimalPrimes.finite_of_isNoetherianRing H).to_subtype
  let ε := v5ComponentCounit I (Bialgebra.counitAlgHom k H) hI
  let Δ := v5ComponentCoproduct I (Bialgebra.counitAlgHom k H) hI hu
    (Bialgebra.comulAlgHom k H) (v5_hopfComponent_doubleCounit (k := k))
  exact v5ProductComponentFixedEquiv_coordinates132
    (v5HopfComponentRegularProduct s hs I hu) (v5HopfComponentAction I) Δ ε
    (v5_component_leftCounit_of_surjective (Ideal.Quotient.mkₐ k I)
      (Ideal.Quotient.mkₐ_surjective k I) ε Δ (fun _ => rfl) (fun _ => rfl))
    (v5HopfComponentRegularProduct_intertwines s hs I hu Δ (fun _ => rfl)) x j
end StrictEUnit
#print axioms StrictEUnit.v5HopfCanonicalFixedCoordinates134
