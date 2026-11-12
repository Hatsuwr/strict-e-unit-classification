import ComplexPolynomialSystemBounds

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

def clearedSystemNormConstant {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) : ℝ :=
  1 + ‖(t.coeff 0)⁻¹‖ *
    (clearedSystemTailNorm t D + clearedSystemMatrixNorm U D)

theorem clearedSystemNormConstant_one_le {r : ℕ} (t : Polynomial ℂ)
    (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (D : ℕ) :
    1 ≤ clearedSystemNormConstant t U D := by
  have hp := mul_nonneg (norm_nonneg ((t.coeff 0)⁻¹))
    (add_nonneg (clearedSystemTailNorm_nonneg t D) (clearedSystemMatrixNorm_nonneg U D))
  dsimp only [clearedSystemNormConstant]
  linarith

/-- Complex norm bounds are derived from the actual cleared system and its
normalization, rather than supplied as an arithmetic-family premise. -/
theorem clearedPolynomialSystem_coeff_norm_bound {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries ℂ))
    (ht0 : t.coeff 0 ≠ 0) (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (hode : ∀ i j, (t : PowerSeries ℂ) * PowerSeries.derivative ℂ (Z i j) =
      ∑ l : Fin r, (U i l : PowerSeries ℂ) * Z l j)
    (hZ0 : Z.map (PowerSeries.constantCoeff ℂ) = 1) :
    ∀ m i j, ‖PowerSeries.coeff ℂ m (Z i j)‖ ≤
      (clearedSystemNormConstant t U D)^m := by
  classical
  let C := clearedSystemNormConstant t U D
  have hC : 1 ≤ C := clearedSystemNormConstant_one_le t U D
  have hb : ∀ (m : ℕ) (i j : Fin r),
      ‖(PowerSeries.coeff ℂ m (Z i j))‖ ≤ C^m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i j
      cases m with
      | zero =>
        have hz := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M i j) hZ0
        change PowerSeries.constantCoeff ℂ (Z i j) = (1 : Matrix (Fin r) (Fin r) ℂ) i j at hz
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hz, Matrix.one_apply]
        split_ifs <;> simp
      | succ n =>
        have hprev : ∀ m, m ≤ n → ∀ i j,
            ‖(PowerSeries.coeff ℂ m (Z i j))‖ ≤ C^n := by
          intro m hm i j
          exact (ih m (Nat.lt_succ_of_le hm) i j).trans (pow_le_pow_right₀ hC hm)
        calc
          _ ≤ ‖(t.coeff 0)⁻¹‖ *
              (clearedSystemTailNorm t D + clearedSystemMatrixNorm U D) * C^n :=
            clearedPolynomialSystem_complex_step t U Z ht0 D htdeg hUdeg hode
              C hC n hprev i j
          _ ≤ C * C^n := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_trans zero_le_one hC) n)
            dsimp only [C, clearedSystemNormConstant]
            linarith
          _ = C^(n+1) := by rw [pow_succ]; ring
  intro m i j
  exact hb m i j

/-- A finite polynomial matrix has an internally constructed common degree. -/
theorem complex_exists_clearedSystem_common_degree {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) :
    ∃ D : ℕ, t.natDegree ≤ D ∧ ∀ i l, (U i l).natDegree ≤ D := by
  classical
  let d := Finset.univ.sup (fun ij : Fin r × Fin r => (U ij.1 ij.2).natDegree)
  refine ⟨d+t.natDegree,Nat.le_add_left _ _,?_⟩
  intro i l
  have h : (U i l).natDegree ≤ d :=
    Finset.le_sup (f := fun ij : Fin r × Fin r => (U ij.1 ij.2).natDegree)
      (Finset.mem_univ (i,l))
  exact h.trans (Nat.le_add_right _ _)

/-- The SAME constructed ordinary fundamental matrix has a common geometric
norm bound at every complex ordinary center, for every coefficient.
The point and the original clearing data are retained literally. -/
theorem complexOrdinaryPoint_fundamental_norm_bound {r : ℕ}
    (t : Polynomial ℂ) (U : Matrix (Fin r) (Fin r) (Polynomial ℂ)) (α : ℂ)
    (hα : t.eval α ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m i j,
      ‖PowerSeries.coeff ℂ m
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j)‖ ≤ C^m := by
  let tα := ordinaryPointPolynomialShift α t
  let Uα : Matrix (Fin r) (Fin r) (Polynomial ℂ) :=
    fun i l => ordinaryPointPolynomialShift α (U i l)
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  obtain ⟨D,htdeg,hUdeg⟩ := complex_exists_clearedSystem_common_degree tα Uα
  have h0 : tα.coeff 0 = t.eval α := ordinaryPointPolynomialSeries_constantCoeff α t
  have ht0 : tα.coeff 0 ≠ 0 := by rw [h0]; exact hα
  have hode : ∀ i j, (tα : PowerSeries ℂ) * PowerSeries.derivative ℂ (Z i j) =
      ∑ l, (Uα i l : PowerSeries ℂ) * Z l j :=
    ordinaryPointClearedMatrix_fundamental_cleared t U α hα
  refine ⟨clearedSystemNormConstant tα Uα D,
    clearedSystemNormConstant_one_le tα Uα D,?_⟩
  exact clearedPolynomialSystem_coeff_norm_bound tα Uα Z ht0 D htdeg hUdeg hode
    (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))

end StrictEUnit
end
