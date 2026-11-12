import AlgebraicPoint

/-! Algebraic points avoiding a nonzero element of a finite-type domain.
The point is derived from the Jacobson property, not assumed. -/
noncomputable section
namespace StrictEUnit
variable {k B : Type*} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

theorem exists_algebraic_point_avoiding (f : B) (hf : f ≠ 0) :
    ∃ p : B →ₐ[k] k, p f ≠ 0 := by
  letI : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k) (B := B)
  have hj : (⊥ : Ideal B).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_noZeroDivisors]
  obtain ⟨m, ⟨_, hm⟩, hfm⟩ :=
    (Ideal.eq_jacobson_iff_not_mem.mp hj) f (by simpa using hf)
  letI : m.IsMaximal := hm
  refine ⟨maximalIdealPoint (k := k) m, ?_⟩
  intro hz
  apply hfm
  rw [← maximalIdealPoint_ker (k := k) m]
  exact hz

theorem exists_algebraic_point_avoiding_pair (f g : B) (hf : f ≠ 0) (hg : g ≠ 0) :
    ∃ p : B →ₐ[k] k, p f ≠ 0 ∧ p g ≠ 0 := by
  obtain ⟨p, hp⟩ := exists_algebraic_point_avoiding (k := k) (f * g) (mul_ne_zero hf hg)
  exact ⟨p, (mul_ne_zero_iff.mp (by simpa only [map_mul] using hp))⟩
end StrictEUnit
#print axioms StrictEUnit.exists_algebraic_point_avoiding
#print axioms StrictEUnit.exists_algebraic_point_avoiding_pair
