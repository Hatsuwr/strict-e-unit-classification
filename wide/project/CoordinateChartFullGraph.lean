import DerivativeStableNormalizedGraph

/-!
The full-coordinate graph of a coordinate chart on a subspace.
The second block keeps ALL original ambient coordinates, including pivots.
Its stability is derived from stability of the original subspace.
-/
noncomputable section
namespace StrictEUnit

/-- The basis matrix of the inverse chart is literally its full-coordinate
linear graph, not a complementary-coordinate projection. -/
theorem coordinateChart_fullGraph_apply
    {F : Type*} [Field F] {r s : ℕ}
    (E : Submodule F (Fin r → F)) (e : E ≃ₗ[F] (Fin s → F))
    (b : Basis (Fin s) F E)
    (hbe : ∀ i, e (b i) = (Pi.basisFun F (Fin s)) i)
    (x : Fin s → F) :
    normalizedGraphMap (fun j i => (b i : Fin r → F) j) x =
      (x, ((e.symm x : E) : Fin r → F)) := by
  classical
  let L : (Fin s → F) →ₗ[F] ((Fin s → F) × (Fin r → F)) :=
    (LinearMap.id : (Fin s → F) →ₗ[F] (Fin s → F)).prod
      (E.subtype.comp e.symm.toLinearMap)
  have hL : normalizedGraphMap (fun j i => (b i : Fin r → F) j) = L := by
    apply (Pi.basisFun F (Fin s)).ext
    intro i
    rw [normalizedGraphMap_basisFun]
    apply Prod.ext
    · rfl
    · change (b i : Fin r → F) =
        ((e.symm ((Pi.basisFun F (Fin s)) i) : E) : Fin r → F)
      rw [← hbe i, e.symm_apply_apply]
  change normalizedGraphMap (fun j i => (b i : Fin r → F) j) x = L x
  exact congrArg (fun f : (Fin s → F) →ₗ[F]
    ((Fin s → F) × (Fin r → F)) => f x) hL

/-- A genuine derivation preserving the original subspace also preserves its
full-coordinate graph. The pivot projection is used to identify the derivative
of the chart coordinates; no linearity over the differential field is assumed. -/
theorem coordinateChart_fullGraph_stable
    {k F : Type*} [CommRing k] [Field F] [Algebra k F] {r s : ℕ}
    (d : Derivation k F F) (E : Submodule F (Fin r → F))
    (p : Fin s ↪ Fin r) (e : E ≃ₗ[F] (Fin s → F))
    (b : Basis (Fin s) F E)
    (he : ∀ v : E, ∀ i : Fin s, e v i = (v : Fin r → F) (p i))
    (hbe : ∀ i, e (b i) = (Pi.basisFun F (Fin s)) i)
    (hstable : ∀ v : Fin r → F, v ∈ E → (fun j => d (v j)) ∈ E) :
    ∀ v : (Fin s → F) × (Fin r → F),
      v ∈ LinearMap.range (normalizedGraphMap (fun j i => (b i : Fin r → F) j)) →
      ((fun i => d (v.1 i)), (fun j => d (v.2 j))) ∈
        LinearMap.range (normalizedGraphMap (fun j i => (b i : Fin r → F) j)) := by
  classical
  intro v hv
  obtain ⟨x, rfl⟩ := (LinearMap.mem_range).mp hv
  rw [coordinateChart_fullGraph_apply E e b hbe x]
  let u : E := ⟨fun j => d (((e.symm x : E) : Fin r → F) j),
    hstable (e.symm x) (e.symm x).property⟩
  apply (LinearMap.mem_range).mpr
  refine ⟨e u, ?_⟩
  rw [coordinateChart_fullGraph_apply E e b hbe (e u), e.symm_apply_apply]
  apply Prod.ext
  · funext i
    change e u i = d (x i)
    rw [he]
    change d (((e.symm x : E) : Fin r → F) (p i)) = d (x i)
    have hi := he (e.symm x) i
    rw [e.apply_symm_apply] at hi
    rw [← hi]
  · rfl

end StrictEUnit
end
