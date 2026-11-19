import GeneratedEntireLaurentClosure
import AbsoluteRelationIdeal

/-! New reconstruction, not recovered historical source. The retained
55-line absolute-primality tail is appended below byte-for-byte unchanged.
Relative closure is derived in GeneratedEntireLaurentClosure from genuine
entire-fraction transfer, analytic monic rigidity, and coefficient descent. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
namespace StrictEUnit

theorem actual_entire_relation_ideal_map_isPrime
    (k : Subfield ℂ) {σ : Type*} [Finite σ]
    (f : σ → subfieldEntireFunctionAlgebra k)
    (L : Type*) [Field L] [Algebra (RatFunc k) L] :
    ((RingHom.ker
      (MvPolynomial.eval₂Hom
        (algebraMap (RatFunc k) (LaurentSeries k))
        (fun i => stage14_subfieldEntireLaurentAlgHom k (f i)))).map
      (MvPolynomial.map (algebraMap (RatFunc k) L))).IsPrime := by
  let E : IntermediateField (RatFunc k) (LaurentSeries k) :=
    generatedEntireLaurentField k (Set.range f)
  letI : Algebra (RatFunc k) E := E.toSubalgebra.algebra
  letI : CharZero (RatFunc k) :=
    charZero_of_injective_algebraMap (algebraMap k (RatFunc k)).injective
  letI : IsIntegrallyClosedIn (RatFunc k) E :=
    generatedEntireLaurentField_integrallyClosedIn k (Set.range f)
  let y : σ → E := fun i =>
    ⟨stage14_subfieldEntireLaurentAlgHom k (f i),
      IntermediateField.subset_adjoin (RatFunc k) _
        ⟨f i, ⟨i, rfl⟩, rfl⟩⟩
  have hcomp :
      E.val.toRingHom.comp
        (MvPolynomial.eval₂Hom (algebraMap (RatFunc k) E) y) =
      MvPolynomial.eval₂Hom
        (algebraMap (RatFunc k) (LaurentSeries k))
        (fun i => stage14_subfieldEntireLaurentAlgHom k (f i)) := by
    rw [MvPolynomial.comp_eval₂Hom]
    rfl
  have hker :
      RingHom.ker
        (MvPolynomial.eval₂Hom
          (algebraMap (RatFunc k) (LaurentSeries k))
          (fun i => stage14_subfieldEntireLaurentAlgHom k (f i))) =
      RingHom.ker
        (MvPolynomial.eval₂Hom (algebraMap (RatFunc k) E) y) := by
    rw [← hcomp]
    exact RingHom.ker_comp_of_injective _ E.val.injective
  rw [hker]
  exact finite_relation_ideal_map_isPrime
    (F := RatFunc k) (E := E) y L

/-- Every specified field embedding is allowed, including the translated
ordinary-point embedding, rather than only the standard Laurent inclusion. -/
theorem actual_entire_relation_ideal_map_ringHom_isPrime
    (k : Subfield ℂ) {σ : Type*} [Finite σ]
    (f : σ → subfieldEntireFunctionAlgebra k)
    {L : Type*} [Field L] (φ : RatFunc k →+* L) :
    ((RingHom.ker
      (MvPolynomial.eval₂Hom
        (algebraMap (RatFunc k) (LaurentSeries k))
        (fun i => stage14_subfieldEntireLaurentAlgHom k (f i)))).map
      (MvPolynomial.map φ)).IsPrime := by
  letI : Algebra (RatFunc k) L := φ.toAlgebra
  exact actual_entire_relation_ideal_map_isPrime k f L

end StrictEUnit
