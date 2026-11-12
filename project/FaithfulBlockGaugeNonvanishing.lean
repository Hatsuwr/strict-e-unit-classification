import FaithfulLinearRelationBaseChange
import BlockFundamentalSupport

/-! A variable from a linearly independent block cannot belong to the gauged
extension of the literal functional relation ideal. Only the selected block is
independent. Neither joint independence nor primality is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix Classical
namespace StrictEUnit

theorem matrixLinearForm_eq_block_sum
    {R ι κ : Type*} [CommRing R] [Fintype ι]
    (A : Matrix ι ι R) (b : ι → κ) (i : ι)
    (hA : ∀ j, b i ≠ b j → A i j = 0) :
    matrixLinearForm A i =
      ∑ j : {j // b j = b i}, MvPolynomial.C (A i j.val) * MvPolynomial.X j.val := by
  classical
  unfold matrixLinearForm
  rw [← Fintype.sum_subtype_add_sum_subtype (fun j => b j = b i)
    (fun j => MvPolynomial.C (A i j) * MvPolynomial.X j)]
  have hz : (∑ j : {j // ¬ b j = b i},
      MvPolynomial.C (A i j.val) * MvPolynomial.X j.val) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hA j.val (Ne.symm j.property), map_zero, zero_mul]
  rw [hz, add_zero]

/-- Pulling a variable back through the gauge produces a nonzero inverse row
supported on the same block. Faithful scalar extension forbids that relation. -/
theorem variable_not_mem_block_gauge_relationIdeal
    {F E L ι κ : Type*} [Field F] [CommRing E] [Algebra F E]
    [CommRing L] [Nontrivial L] [Algebra F L]
    [Fintype ι] [DecidableEq ι]
    (y : ι → E) (b : ι → κ) (u : (Matrix ι ι L)ˣ)
    (hu : ∀ a z, b a ≠ b z → (u : Matrix ι ι L) a z = 0)
    (i : ι)
    (hy : LinearIndependent F (fun j : {j // b j = b i} => y j.val)) :
    MvPolynomial.X i ∉
      ((RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
        (MvPolynomial.map (algebraMap F L))).map
          (matrixPolynomialSubst (u : Matrix ι ι L)).toRingHom := by
  classical
  intro hXi
  let I : Ideal (MvPolynomial ι L) :=
    (RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
      (MvPolynomial.map (algebraMap F L))
  let e := matrixPolynomialGaugeEquiv u
  have hback : e.symm (MvPolynomial.X i) ∈ I :=
    (Ideal.symm_apply_mem_of_equiv_iff (f := e.toRingEquiv)).mpr hXi
  change matrixPolynomialSubst
    ((u⁻¹ : (Matrix ι ι L)ˣ) : Matrix ι ι L) (MvPolynomial.X i) ∈ I at hback
  rw [matrixPolynomialSubst_X] at hback
  rw [matrixLinearForm_eq_block_sum
    ((u⁻¹ : (Matrix ι ι L)ˣ) : Matrix ι ι L) b i
    (unitMatrix_inv_preserves_blocks b u hu i)] at hback
  have hc := relationIdeal_map_linearForm_coefficients_zero
    (F := F) (E := E) (L := L) y
    (fun j : {j // b j = b i} => j.val) hy
    (fun j : {j // b j = b i} =>
      ((u⁻¹ : (Matrix ι ι L)ˣ) : Matrix ι ι L) i j.val) hback
  obtain ⟨j, hji, hj⟩ := unitMatrix_inv_row_nonzero_in_block b u hu i
  exact hj (hc ⟨j, hji⟩)

/-- The coefficient embedding is explicit, so this applies to the translated
rational-function embedding as well as the standard Laurent embedding. -/
theorem variable_not_mem_block_gauge_relationIdeal_ringHom
    {F E L ι κ : Type*} [Field F] [CommRing E] [Algebra F E]
    [CommRing L] [Nontrivial L] [Fintype ι] [DecidableEq ι]
    (φ : F →+* L) (y : ι → E) (b : ι → κ) (u : (Matrix ι ι L)ˣ)
    (hu : ∀ a z, b a ≠ b z → (u : Matrix ι ι L) a z = 0)
    (i : ι)
    (hy : LinearIndependent F (fun j : {j // b j = b i} => y j.val)) :
    MvPolynomial.X i ∉
      ((RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
        (MvPolynomial.map φ)).map
          (matrixPolynomialSubst (u : Matrix ι ι L)).toRingHom := by
  letI : Algebra F L := φ.toAlgebra
  exact variable_not_mem_block_gauge_relationIdeal y b u hu i hy

theorem variable_not_mem_block_gauge_relationIdeal_of_isUnit
    {F E L ι κ : Type*} [Field F] [CommRing E] [Algebra F E]
    [CommRing L] [Nontrivial L] [Fintype ι] [DecidableEq ι]
    (φ : F →+* L) (y : ι → E) (b : ι → κ)
    (W : Matrix ι ι L) (hW : IsUnit W)
    (hblock : ∀ a z, b a ≠ b z → W a z = 0)
    (i : ι)
    (hy : LinearIndependent F (fun j : {j // b j = b i} => y j.val)) :
    MvPolynomial.X i ∉
      ((RingHom.ker (MvPolynomial.eval₂Hom (algebraMap F E) y)).map
        (MvPolynomial.map φ)).map (matrixPolynomialSubst W).toRingHom := by
  obtain ⟨u, rfl⟩ := hW
  exact variable_not_mem_block_gauge_relationIdeal_ringHom φ y b u hblock i hy

/-- Specialization to the actual normalized ordinary-point gauge. The same
clearing data derives its support, so no separate matrix or inverse is supplied. -/
theorem ordinaryPointGaugedIdeal_variable_not_mem_of_block_independent
    {K E κ : Type*} [Field K] [CharZero K] [CommRing E]
    [Algebra (RatFunc K) E] {r : ℕ}
    (y : Fin r → E) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ a z, algebraMap (Polynomial K) (RatFunc K) (U a z) =
      algebraMap (Polynomial K) (RatFunc K) t * A a z)
    (α : K) (b : Fin r → κ) (hA : ∀ a z, b a ≠ b z → A a z = 0)
    (i : Fin r)
    (hy : LinearIndependent (RatFunc K)
      (fun j : {j // b j = b i} => y j.val)) :
    MvPolynomial.X i ∉ ordinaryPointGaugedIdeal t U α
      (RingHom.ker (MvPolynomial.eval₂Hom (algebraMap (RatFunc K) E) y)) := by
  exact variable_not_mem_block_gauge_relationIdeal_of_isUnit
    (ordinaryPointRationalMap α) y b (ordinaryPointLaurentFundamental t U α)
    (ordinaryPointLaurentFundamental_isUnit t U α)
    (ordinaryPointLaurentFundamental_preserves_blocks_of_clearing A t U hclear α b hA)
    i hy

end StrictEUnit
end
