import Stage14PolynomialScalarODEClosure

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {k R : Type*} [Field k] [CommRing R]
  [Algebra k R] [Algebra (RatFunc k) R] [IsScalarTower k (RatFunc k) R]

/-- A displayed finite rational differential system produces a genuinely
nonzero polynomial scalar ODE for every component. No independence required. -/
theorem finiteConnection_polynomialScalarRelation
    {ι : Type*} [Fintype ι]
    (dB : Derivation k (RatFunc k) (RatFunc k)) (d : Derivation k R R)
    (hcompat : ∀ b,d (algebraMap (RatFunc k) R b)=algebraMap (RatFunc k) R (dB b))
    (C : Matrix ι ι (RatFunc k)) (y : ι →R)
    (hy : ∀ i,d (y i)=∑ j,C i j • y j) :
    ∀ i,HasPolynomialScalarDifferentialRelation d (y i) := by
  intro i
  apply finiteDifferentialSpan_polynomialScalarRelation
  refine ⟨Submodule.span (RatFunc k) (Set.range y),Submodule.fg_span (Set.finite_range y),?_,
    Submodule.subset_span ⟨i,rfl⟩⟩
  apply differential_span_stable dB d hcompat
  rintro x ⟨j,rfl⟩
  rw [hy j]
  exact Submodule.sum_mem _ (fun l _ =>Submodule.smul_mem _ _ (Submodule.subset_span ⟨l,rfl⟩))
end StrictEUnit
end
