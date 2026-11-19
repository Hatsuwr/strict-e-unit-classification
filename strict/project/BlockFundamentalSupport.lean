import OrdinaryPointPolynomialIdealGauge
import Mathlib.Algebra.Group.Commute.Units

/-! The literal normalized fundamental matrix preserves any supplied partition
of the system indices. Its unit inverse preserves the same partition and has
no zero row. No independence of different blocks is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

theorem formalFundamentalCoeff_preserves_blocks
    {K κ : Type*} [Field K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (b : Fin r → κ)
    (hA : ∀ i j, b i ≠ b j → A i j = 0) :
    ∀ n i j, b i ≠ b j → formalFundamentalCoeff A n i j = 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro i j hij
    cases n with
    | zero =>
      have hne : i ≠ j := fun he => hij (congrArg b he)
      simp only [formalFundamentalCoeff_zero, Matrix.one_apply, if_neg hne]
    | succ n =>
      rw [formalFundamentalCoeff_succ, Matrix.smul_apply, smul_eq_mul]
      suffices hs : (∑ k : Fin (n+1),
          A.map (PowerSeries.coeff K k.val) * formalFundamentalCoeff A (n-k.val)) i j = 0 by
        rw [hs, mul_zero]
      rw [Matrix.sum_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro l _
      by_cases hil : b i = b l
      · have hlj : b l ≠ b j := fun he => hij (hil.trans he)
        rw [ih (n-k.val) (by omega) l j hlj, mul_zero]
      · rw [Matrix.map_apply, hA i l hil, map_zero, zero_mul]

theorem formalFundamentalMatrix_preserves_blocks
    {K κ : Type*} [Field K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (PowerSeries K)) (b : Fin r → κ)
    (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) :
    formalFundamentalMatrix A i j = 0 := by
  apply PowerSeries.ext
  intro n
  rw [formalFundamentalMatrix_coeff,
    formalFundamentalCoeff_preserves_blocks A b hA n i j hij, map_zero]

theorem ordinaryPointClearedMatrix_preserves_blocks
    {K κ : Type*} [Field K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (b : Fin r → κ)
    (hU : ∀ i j, b i ≠ b j → U i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) :
    ordinaryPointClearedMatrix t U α i j = 0 := by
  change ordinaryPointPolynomialSeriesHom α (U i j) *
    (ordinaryPointPolynomialSeries α t)⁻¹ = 0
  rw [hU i j hij, map_zero, zero_mul]

theorem ordinaryPointLaurentFundamental_preserves_blocks
    {K κ : Type*} [Field K] [CharZero K] {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (b : Fin r → κ)
    (hU : ∀ i j, b i ≠ b j → U i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) :
    ordinaryPointLaurentFundamental t U α i j = 0 := by
  change HahnSeries.ofPowerSeries ℤ K
    (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j) = 0
  rw [formalFundamentalMatrix_preserves_blocks
    (ordinaryPointClearedMatrix t U α) b
    (ordinaryPointClearedMatrix_preserves_blocks t U α b hU) i j hij, map_zero]

/-- The same clearing identity forces the polynomial matrix to preserve the
blocks of the rational matrix. No new support hypothesis on U is needed. -/
theorem clearedPolynomialMatrix_preserves_blocks
    {K κ : Type*} [Field K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (b : Fin r → κ) (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) : U i j = 0 := by
  apply RatFunc.algebraMap_injective K
  rw [hclear, hA i j hij, mul_zero, map_zero]

theorem ordinaryPointClearedMatrix_preserves_blocks_of_clearing
    {K κ : Type*} [Field K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (α : K) (b : Fin r → κ) (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) :
    ordinaryPointClearedMatrix t U α i j = 0 :=
  ordinaryPointClearedMatrix_preserves_blocks t U α b
    (clearedPolynomialMatrix_preserves_blocks A t U hclear b hA) i j hij

theorem ordinaryPointLaurentFundamental_preserves_blocks_of_clearing
    {K κ : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (α : K) (b : Fin r → κ) (hA : ∀ i j, b i ≠ b j → A i j = 0)
    (i j : Fin r) (hij : b i ≠ b j) :
    ordinaryPointLaurentFundamental t U α i j = 0 :=
  ordinaryPointLaurentFundamental_preserves_blocks t U α b
    (clearedPolynomialMatrix_preserves_blocks A t U hclear b hA) i j hij

/-- Commutation with each block's diagonal projection is preserved by taking
the inverse of a matrix unit. This derives inverse support without a separate
invertibility assumption on any block. -/
theorem unitMatrix_inv_preserves_blocks
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (b : ι → κ) (u : (Matrix ι ι R)ˣ)
    (hu : ∀ i j, b i ≠ b j → (u : Matrix ι ι R) i j = 0) :
    ∀ i j, b i ≠ b j → ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j = 0 := by
  classical
  intro i j hij
  let d : ι → R := fun k => if b k = b i then 1 else 0
  have hc : Commute (u : Matrix ι ι R) (Matrix.diagonal d) := by
    show (u : Matrix ι ι R) * Matrix.diagonal d =
      Matrix.diagonal d * (u : Matrix ι ι R)
    ext a z
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    by_cases haz : b a = b z
    · have hd : d a = d z := by dsimp only [d]; rw [haz]
      rw [hd]
      exact mul_comm _ _
    · rw [hu a z haz, zero_mul, mul_zero]
  have he := congrArg (fun M : Matrix ι ι R => M i j)
    hc.units_inv_left.eq
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at he
  have hji : b j ≠ b i := Ne.symm hij
  simpa only [d, if_pos rfl, if_neg hji, mul_zero, one_mul] using he.symm

theorem unitMatrix_inv_row_nonzero
    {R ι : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι]
    (u : (Matrix ι ι R)ˣ) (i : ι) :
    ∃ j, ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ j, ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j = 0 := by
    simpa only [not_exists, not_not] using h
  have hu : ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) *
      (u : Matrix ι ι R) = 1 := by simp
  have he := congrArg (fun M : Matrix ι ι R => M i i) hu
  have h01 : (0 : R) = 1 := by
    simpa only [Matrix.mul_apply, hz, zero_mul, Finset.sum_const_zero,
      Matrix.one_apply, if_pos rfl] using he
  exact zero_ne_one h01

/-- The nonzero coefficient occurs in the same block as the chosen row. -/
theorem unitMatrix_inv_row_nonzero_in_block
    {R ι κ : Type*} [CommRing R] [Nontrivial R]
    [Fintype ι] [DecidableEq ι]
    (b : ι → κ) (u : (Matrix ι ι R)ˣ)
    (hu : ∀ i j, b i ≠ b j → (u : Matrix ι ι R) i j = 0)
    (i : ι) :
    ∃ j, b j = b i ∧
      ((u⁻¹ : (Matrix ι ι R)ˣ) : Matrix ι ι R) i j ≠ 0 := by
  obtain ⟨j, hj⟩ := unitMatrix_inv_row_nonzero u i
  refine ⟨j, ?_, hj⟩
  by_contra hji
  exact hj (unitMatrix_inv_preserves_blocks b u hu i j (Ne.symm hji))

end StrictEUnit
end
