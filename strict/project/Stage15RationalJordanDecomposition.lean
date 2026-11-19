import Stage15RationalJordanBasis

/-! A rational diagonal plus commuting nilpotent decomposition of the matrix
of an actual operator, in a basis constructed from its generalized eigenspaces. -/
noncomputable section
namespace StrictEUnit
open Module
open scoped Matrix
variable {k n : Type*} [Field k] [CharZero k] [Fintype n] [DecidableEq n]

omit [CharZero k] in
/-- The diagonal operator acts by its block's rational scalar on the entire
corresponding generalized eigenspace, not merely on the chosen basis vectors. -/
theorem stage15_diagonal_on_generalized_eigenspace
    (f : Module.End k (n → k)) (b : Basis n k (n → k)) (q : n → ℚ)
    (hsupport : ∀ (a : ℚ) (x : n → k),
      x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k)) →
      ∀ i, q i ≠ a → b.repr x i = 0)
    (a : ℚ) (x : n → k)
    (hx : x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k))) :
    Matrix.toLinAlgEquiv b (Matrix.diagonal fun i => (q i : k)) x = (a : k) • x := by
  apply b.repr.injective
  ext i
  have he := LinearMap.toMatrix_mulVec_repr b b
    (Matrix.toLinAlgEquiv b (Matrix.diagonal fun i => (q i : k))) x
  change (LinearMap.toMatrixAlgEquiv b
    (Matrix.toLinAlgEquiv b (Matrix.diagonal fun i => (q i : k)))) *ᵥ b.repr x = _ at he
  rw [LinearMap.toMatrixAlgEquiv_toLinAlgEquiv] at he
  rw [← congrFun he i]
  simp only [Matrix.mulVec_diagonal, map_smul, Finsupp.smul_apply, smul_eq_mul]
  by_cases hi : q i = a
  · rw [hi]
  · rw [hsupport a x hx i hi, mul_zero, mul_zero]

/-- Spanning by rational generalized eigenspaces suffices to construct a basis
and a commuting nilpotent remainder. The original operator is the input. -/
theorem stage15_rational_jordan_decomposition_of_span
    (f : Module.End k (n → k))
    (hspan : (⨆ q : ℚ, f.genEigenspace (q : k) (Module.finrank k (n → k))) = ⊤) :
    ∃ (b : Basis n k (n → k)) (q : n → ℚ) (J : Matrix n n k),
      IsNilpotent J ∧ Commute (Matrix.diagonal fun i => (q i : k)) J ∧
      LinearMap.toMatrixAlgEquiv b f = Matrix.diagonal (fun i => (q i : k)) + J := by
  classical
  obtain ⟨b, q, hb, hs⟩ := stage15_rational_generalized_eigenbasis f hspan
  let D : Matrix n n k := Matrix.diagonal fun i => (q i : k)
  let S : Module.End k (n → k) := Matrix.toLinAlgEquiv b D
  let T : Module.End k (n → k) := f - S
  have hS (a : ℚ) (x : n → k)
      (hx : x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k))) :
      S x = (a : k) • x := stage15_diagonal_on_generalized_eigenspace f b q hs a x hx
  have hT (a : ℚ) (x : n → k)
      (hx : x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k))) :
      T x = (f - (a : k) • 1) x := by
    simp only [T, LinearMap.sub_apply, hS a x hx, LinearMap.smul_apply, Module.End.one_apply]
  have hp (a : ℚ) (r : ℕ) (x : n → k)
      (hx : x ∈ f.genEigenspace (a : k) (Module.finrank k (n → k))) :
      (T ^ r) x = ((f - (a : k) • 1) ^ r) x := by
    induction r generalizing x with
    | zero => rfl
    | succ r ih =>
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT a x hx]
      apply ih
      exact f.mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f (a : k))
        (a : k) (Module.finrank k (n → k)) hx
  have hn : IsNilpotent T := by
    refine ⟨Module.finrank k (n → k), ?_⟩
    apply b.ext
    intro i
    rw [LinearMap.zero_apply, hp (q i) _ (b i) (hb i)]
    exact Module.End.mem_genEigenspace_nat.mp (hb i)
  have hcomm : Commute S f := by
    apply b.ext
    intro i
    change S (f (b i)) = f (S (b i))
    rw [hS (q i) (b i) (hb i), map_smul]
    exact hS (q i) (f (b i))
      (f.mapsTo_genEigenspace_of_comm (Commute.refl f) _ _ (hb i))
  have hST : Commute S T := hcomm.sub_right (Commute.refl S)
  refine ⟨b, q, LinearMap.toMatrixAlgEquiv b T,
    hn.map (LinearMap.toMatrixAlgEquiv b).toRingHom, ?_, ?_⟩
  · have hm : Commute (LinearMap.toMatrixAlgEquiv b S) (LinearMap.toMatrixAlgEquiv b T) :=
      hST.map (LinearMap.toMatrixAlgEquiv b).toRingHom
    simpa only [S, LinearMap.toMatrixAlgEquiv_toLinAlgEquiv, D] using hm
  · simp only [T, map_sub, S, LinearMap.toMatrixAlgEquiv_toLinAlgEquiv, D,
      add_sub_cancel]

/-- In an algebraically closed characteristic-zero field, rationality of all
actual eigenvalues yields the genuine rational diagonal/nilpotent form. -/
theorem stage15_rational_jordan_decomposition [IsAlgClosed k]
    (f : Module.End k (n → k))
    (hrat : ∀ a : k, f.HasEigenvalue a → ∃ q : ℚ, (q : k) = a) :
    ∃ (b : Basis n k (n → k)) (q : n → ℚ) (J : Matrix n n k),
      IsNilpotent J ∧ Commute (Matrix.diagonal fun i => (q i : k)) J ∧
      LinearMap.toMatrixAlgEquiv b f = Matrix.diagonal (fun i => (q i : k)) + J :=
  stage15_rational_jordan_decomposition_of_span f
    (stage15_rational_generalized_eigenspaces_span f hrat)

end StrictEUnit
