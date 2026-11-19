import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section
open scoped TensorProduct
namespace StrictEUnit

variable {k H N ι : Type*} [Field k] [CommRing H] [CommRing N]
  [Algebra k H] [Algebra k N]

/-- Projection to a component, expressed using a fixed product trivialization. -/
def v5ProductProjection (e : H ≃ₐ[k] (ι → N)) (i : ι) : H →ₐ[k] N :=
  (Pi.evalAlgHom k (fun _ : ι => N) i).comp e.toAlgHom

theorem v5_product_tensor_ext [Finite ι] (e : H ≃ₐ[k] (ι → N))
    (x y : H ⊗[k] N)
    (h : ∀ i, Algebra.TensorProduct.map (v5ProductProjection e i) (AlgHom.id k N) x =
      Algebra.TensorProduct.map (v5ProductProjection e i) (AlgHom.id k N) y) :
    x = y := by
  classical
  letI := Fintype.ofFinite ι
  let c := (Algebra.TensorProduct.congr e (AlgEquiv.refl : N ≃ₐ[k] N)).trans
    (Algebra.TensorProduct.comm k (ι → N) N)
  let E := c.trans (Algebra.TensorProduct.piRight k k N (fun _ : ι => N))
  have hE (z : H ⊗[k] N) (i : ι) :
      E z i = Algebra.TensorProduct.comm k N N
        (Algebra.TensorProduct.map (v5ProductProjection e i) (AlgHom.id k N) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  apply E.injective
  funext i
  rw [hE, hE, h i]

def v5ComponentLeftScalar (ε : N →ₐ[k] k) : N ⊗[k] N →ₐ[k] N :=
  Algebra.TensorProduct.lift ((Algebra.ofId k N).comp ε) (AlgHom.id k N) (fun _ _ => .all _ _)

theorem v5ComponentLeftScalar_tmul (ε : N →ₐ[k] k) (a b : N) :
    v5ComponentLeftScalar ε (a ⊗ₜ[k] b) = algebraMap k N (ε a) * b := rfl

/-- Invariants of an action which is the right regular coaction on each
component. The tensor projection condition is the data to verify for a
specific component trivialization, not an assumption about fixed elements. -/
theorem v5_product_component_fixed_iff [Finite ι]
    (e : H ≃ₐ[k] (ι → N))
    (ρ : H →ₐ[k] H ⊗[k] N) (Δ : N →ₐ[k] N ⊗[k] N) (ε : N →ₐ[k] k)
    (hleft : ∀ n, v5ComponentLeftScalar ε (Δ n) = n)
    (he : ∀ x i, Algebra.TensorProduct.map (v5ProductProjection e i) (AlgHom.id k N) (ρ x) =
      Δ (e x i)) (x : H) :
    ρ x = x ⊗ₜ[k] 1 ↔ ∀ i, e x i = algebraMap k N (ε (e x i)) := by
  constructor
  · intro hx i
    have heq := he x i
    rw [hx, Algebra.TensorProduct.map_tmul] at heq
    have hz := congrArg (v5ComponentLeftScalar ε) heq
    simpa only [v5ProductProjection, AlgHom.comp_apply, Pi.evalAlgHom, AlgHom.id_apply,
      v5ComponentLeftScalar_tmul, mul_one, hleft] using hz.symm
  · intro h
    apply v5_product_tensor_ext e
    intro i
    rw [he, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change Δ (e x i) = (e x i) ⊗ₜ[k] (1 : N)
    rw [h i, Δ.commutes]
    rfl

private def v5ProductToScalars (e : H ≃ₐ[k] (ι → N)) (ε : N →ₐ[k] k) :
    H →ₐ[k] (ι → k) :=
  Pi.algHom k (fun _ : ι => k) (fun i => ε.comp (v5ProductProjection e i))

private def v5ProductFromScalars (e : H ≃ₐ[k] (ι → N)) : (ι → k) →ₐ[k] H :=
  e.symm.toAlgHom.comp (Pi.algHom k (fun _ : ι => N)
    (fun i => (Algebra.ofId k N).comp (Pi.evalAlgHom k (fun _ : ι => k) i)))

private theorem v5ProductFromScalars_apply (e : H ≃ₐ[k] (ι → N)) (x : ι → k) (i : ι) :
    e (v5ProductFromScalars e x) i = algebraMap k N (x i) := by
  simp [v5ProductFromScalars, Pi.evalAlgHom]
  rfl

/-- The invariants of a finite product of regular component charts are its
componentwise scalars, as an algebra equivalence rather than a set equality. -/
def v5ProductComponentFixedEquiv [Finite ι]
    (e : H ≃ₐ[k] (ι → N))
    (ρ : H →ₐ[k] H ⊗[k] N) (Δ : N →ₐ[k] N ⊗[k] N) (ε : N →ₐ[k] k)
    (hleft : ∀ n, v5ComponentLeftScalar ε (Δ n) = n)
    (he : ∀ x i, Algebra.TensorProduct.map (v5ProductProjection e i) (AlgHom.id k N) (ρ x) =
      Δ (e x i)) :
    AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) ≃ₐ[k] (ι → k) := by
  let Q := AlgHom.equalizer ρ (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N)
  let m : Q →ₐ[k] (ι → k) := (v5ProductToScalars e ε).comp Q.val
  have hfix (x : Q) (i : ι) : e x i = algebraMap k N (m x i) :=
    (v5_product_component_fixed_iff e ρ Δ ε hleft he x).mp x.property i
  refine AlgEquiv.ofBijective m ⟨?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    apply e.injective
    funext i
    rw [hfix x i, hfix y i, congrFun h i]
  · intro z
    let x := v5ProductFromScalars e z
    have hx (i : ι) : e x i = algebraMap k N (z i) := v5ProductFromScalars_apply e z i
    have hε (i : ι) : ε (e x i) = z i := by
      rw [hx i, ε.commutes]
      rfl
    have hp : x ∈ Q := by
      refine (v5_product_component_fixed_iff e ρ Δ ε hleft he x).mpr (fun i => ?_)
      exact (hx i).trans (congrArg (algebraMap k N) (hε i).symm)
    exact ⟨⟨x, hp⟩, funext hε⟩

section LeftCounit
variable {K B S : Type*} [Field K] [CommRing B] [Bialgebra K B]
  [CommRing S] [Algebra K S]

/-- The left scalar counit law survives every compatible surjective quotient
of a bialgebra. The quotient need not have been made a bialgebra instance. -/
theorem v5_component_leftCounit_of_surjective
    (q : B →ₐ[K] S) (hq : Function.Surjective q)
    (ε : S →ₐ[K] K) (Δ : S →ₐ[K] S ⊗[K] S)
    (hε : ∀ x, ε (q x) = Bialgebra.counitAlgHom K B x)
    (hΔ : ∀ x, Δ (q x) = Algebra.TensorProduct.map q q (Bialgebra.comulAlgHom K B x))
    (x : S) : v5ComponentLeftScalar ε (Δ x) = x := by
  obtain ⟨y, rfl⟩ := hq x
  have he (z : B ⊗[K] B) :
      v5ComponentLeftScalar ε (Algebra.TensorProduct.map q q z) =
      q (TensorProduct.lid K B ((Coalgebra.counit (R := K)).rTensor B z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b =>
      simp only [Algebra.TensorProduct.map_tmul, v5ComponentLeftScalar_tmul, hε,
        LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Algebra.smul_def, map_mul,
        AlgHom.commutes]; rfl
  rw [hΔ, he]
  change q (TensorProduct.lid K B ((Coalgebra.counit (R := K)).rTensor B (Coalgebra.comul y))) = q y
  rw [Coalgebra.rTensor_counit_comul]
  simp
end LeftCounit

end StrictEUnit
#print axioms StrictEUnit.v5_product_tensor_ext
#print axioms StrictEUnit.v5_product_component_fixed_iff
#print axioms StrictEUnit.v5ProductComponentFixedEquiv
#print axioms StrictEUnit.v5_component_leftCounit_of_surjective
