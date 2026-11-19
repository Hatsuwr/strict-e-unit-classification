import V5ComponentRegular
import V5ProductComponentInvariants
import V5WideComponentProduct

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

variable {k H : Type*} [Field k] [IsAlgClosed k] [CommRing H] [HopfAlgebra k H]
    [Algebra.FiniteType k H] [IsReduced H]

def v5HopfComponentMarkedPoint (P : minimalPrimes H) : H →ₐ[k] k :=
  letI := Algebra.FiniteType.isNoetherianRing k H
  Classical.choose (v5_minimal_component_unique_point (k := k)
    (minimalPrimes.finite_of_isNoetherianRing H) P P.property)

omit [IsReduced H] in
theorem v5HopfComponentMarkedPoint_ker (P : minimalPrimes H) :
    (P : Ideal H) ≤ RingHom.ker (v5HopfComponentMarkedPoint (k := k) P).toRingHom :=
  letI := Algebra.FiniteType.isNoetherianRing k H
  (Classical.choose_spec (v5_minimal_component_unique_point (k := k)
    (minimalPrimes.finite_of_isNoetherianRing H) P P.property)).1

variable (s : H →ₐ[k] H) (hs : s.toLinearMap = HopfAlgebra.antipode)
  (I : Ideal H)
  (hu : ∀ P ∈ minimalPrimes H, P ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom → P = I)

def v5HopfAllComponentEquiv (P : minimalPrimes H) :
    (H ⧸ (P : Ideal H)) ≃ₐ[k] (H ⧸ I) :=
  v5ComponentTranslateEquiv (Bialgebra.counitAlgHom k H) (v5HopfComponentMarkedPoint P)
    (v5HopfTranslation s hs (v5HopfComponentMarkedPoint P))
    (v5HopfTranslation_at_counit s hs (v5HopfComponentMarkedPoint P))
    P I P.property (v5HopfComponentMarkedPoint_ker P) hu

def v5HopfComponentRegularProduct :
    H ≃ₐ[k] (minimalPrimes H → H ⧸ I) :=
  (v5_hopf_minimalPrimeCRT s hs).trans
    (AlgEquiv.piCongrRight (v5HopfAllComponentEquiv s hs I hu))

theorem v5HopfComponentRegularProduct_apply (x : H) (P : minimalPrimes H) :
    v5HopfComponentRegularProduct s hs I hu x P =
      Ideal.Quotient.mkₐ k I (v5HopfTranslate (v5HopfComponentMarkedPoint (k := k) P) x) :=
  rfl

/-- Right action on H after restriction to the identity component quotient. -/
def v5HopfComponentAction :
    H →ₐ[k] H ⊗[k] (H ⧸ I) :=
  (Algebra.TensorProduct.map (AlgHom.id k H) (Ideal.Quotient.mkₐ k I)).comp
    (Bialgebra.comulAlgHom k H)

theorem v5HopfComponentRegularProduct_intertwines
    (Δ : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (hΔ : ∀ x, Δ (Ideal.Quotient.mkₐ k I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
        (Bialgebra.comulAlgHom k H x))
    (x : H) (P : minimalPrimes H) :
    Algebra.TensorProduct.map (v5ProductProjection (v5HopfComponentRegularProduct s hs I hu) P)
      (AlgHom.id k (H ⧸ I)) (v5HopfComponentAction (k := k) I x) =
    Δ (v5HopfComponentRegularProduct s hs I hu x P) := by
  let q := Ideal.Quotient.mkₐ k I
  let t := v5HopfTranslate (v5HopfComponentMarkedPoint (k := k) P)
  have hπ : v5ProductProjection (v5HopfComponentRegularProduct s hs I hu) P = q.comp t := by
    ext u
    exact v5HopfComponentRegularProduct_apply s hs I hu u P
  rw [hπ, v5HopfComponentRegularProduct_apply, hΔ, v5HopfTranslate_comul]
  change Algebra.TensorProduct.map (q.comp t) (AlgHom.id k (H ⧸ I))
      (Algebra.TensorProduct.map (AlgHom.id k H) q (Bialgebra.comulAlgHom k H x)) =
    Algebra.TensorProduct.map q q (Algebra.TensorProduct.map t (AlgHom.id k H)
      (Bialgebra.comulAlgHom k H x))
  have hcomp : (Algebra.TensorProduct.map (q.comp t) (AlgHom.id k (H ⧸ I))).comp
        (Algebra.TensorProduct.map (AlgHom.id k H) q) =
      (Algebra.TensorProduct.map q q).comp
        (Algebra.TensorProduct.map t (AlgHom.id k H)) := by
    rw [← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp,
      AlgHom.comp_id, AlgHom.comp_id, AlgHom.id_comp]
  exact DFunLike.congr_fun hcomp (Bialgebra.comulAlgHom k H x)

/-- Identity-component invariants of a reduced finite-type Hopf algebra
are the scalar functions on its set of minimal components. -/
def v5HopfComponentFixedEquiv
    (ε : H ⧸ I →ₐ[k] k) (Δ : H ⧸ I →ₐ[k] (H ⧸ I) ⊗[k] (H ⧸ I))
    (hε : ∀ x, ε (Ideal.Quotient.mkₐ k I x) = Bialgebra.counitAlgHom k H x)
    (hΔ : ∀ x, Δ (Ideal.Quotient.mkₐ k I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)
        (Bialgebra.comulAlgHom k H x)) :=
  letI := Algebra.FiniteType.isNoetherianRing k H
  letI := (minimalPrimes.finite_of_isNoetherianRing H).to_subtype
  v5ProductComponentFixedEquiv (v5HopfComponentRegularProduct s hs I hu)
    (v5HopfComponentAction I) Δ ε
    (v5_component_leftCounit_of_surjective (Ideal.Quotient.mkₐ k I)
      (Ideal.Quotient.mkₐ_surjective k I) ε Δ hε hΔ)
    (v5HopfComponentRegularProduct_intertwines s hs I hu Δ hΔ)

/-- Packed specialization with canonical quotient maps, so callers need not
elaborate explicit concrete quotient tensors or their comparison squares. -/
def v5HopfCanonicalComponentFixedEquiv
    (hprime : I.IsPrime)
    (hI : I ≤ RingHom.ker (Bialgebra.counitAlgHom k H).toRingHom) :=
  letI : I.IsPrime := hprime
  letI := v5_primeQuotient_tensorSquare_isDomain (k := k) I
  let ε := Bialgebra.counitAlgHom k H
  let Δ := Bialgebra.comulAlgHom k H
  v5HopfComponentFixedEquiv s hs I hu (v5ComponentCounit I ε hI)
    (v5ComponentCoproduct I ε hI hu Δ (v5_hopfComponent_doubleCounit (k := k)))
    (fun _ => rfl) (fun _ => rfl)

end StrictEUnit
#print axioms StrictEUnit.v5HopfComponentMarkedPoint
#print axioms StrictEUnit.v5HopfComponentRegularProduct
#print axioms StrictEUnit.v5HopfComponentRegularProduct_apply
#print axioms StrictEUnit.v5HopfComponentRegularProduct_intertwines
#print axioms StrictEUnit.v5HopfComponentFixedEquiv
#print axioms StrictEUnit.v5HopfCanonicalComponentFixedEquiv
