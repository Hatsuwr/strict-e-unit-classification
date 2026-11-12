import OrdinaryPointHouseBounds

noncomputable section
open scoped NumberField BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

def clearedSystemHouseConstant {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (D : ℕ) : ℝ :=
  1 + NumberField.house ((t.coeff 0)⁻¹) *
    (clearedSystemTailHouse t D + clearedSystemMatrixHouse U D)

theorem clearedSystemHouseConstant_one_le {r : ℕ} (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (D : ℕ) :
    1 ≤ clearedSystemHouseConstant t U D := by
  have hp := mul_nonneg (NumberField.house_nonneg ((t.coeff 0)⁻¹))
    (add_nonneg (clearedSystemTailHouse_nonneg t D) (clearedSystemMatrixHouse_nonneg U D))
  dsimp only [clearedSystemHouseConstant]
  linarith

/-- Uniform house bounds are derived from the actual cleared system and its
normalization, rather than supplied as an arithmetic-family premise. -/
theorem clearedPolynomialSystem_coeff_house_bound {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (ht0 : t.coeff 0 ≠ 0) (D : ℕ) (htdeg : t.natDegree ≤ D)
    (hUdeg : ∀ i l, (U i l).natDegree ≤ D)
    (hode : ∀ i j, (t : PowerSeries K) * PowerSeries.derivative K (Z i j) =
      ∑ l : Fin r, (U i l : PowerSeries K) * Z l j)
    (hZ0 : Z.map (PowerSeries.constantCoeff K) = 1) :
    ∀ m i j, NumberField.house (PowerSeries.coeff K m (Z i j)) ≤
      (clearedSystemHouseConstant t U D)^m := by
  classical
  let C := clearedSystemHouseConstant t U D
  have hC : 1 ≤ C := clearedSystemHouseConstant_one_le t U D
  have hb : ∀ (σ : K →+* ℂ) (m : ℕ) (i j : Fin r),
      ‖σ (PowerSeries.coeff K m (Z i j))‖ ≤ C^m := by
    intro σ m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro i j
      cases m with
      | zero =>
        have hz := congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j) hZ0
        change PowerSeries.constantCoeff K (Z i j) = (1 : Matrix (Fin r) (Fin r) K) i j at hz
        rw [PowerSeries.coeff_zero_eq_constantCoeff, hz, Matrix.one_apply]
        split_ifs <;> simp
      | succ n =>
        have hprev : ∀ m, m ≤ n → ∀ i j,
            ‖σ (PowerSeries.coeff K m (Z i j))‖ ≤ C^n := by
          intro m hm i j
          exact (ih m (Nat.lt_succ_of_le hm) i j).trans (pow_le_pow_right₀ hC hm)
        calc
          _ ≤ NumberField.house ((t.coeff 0)⁻¹) *
              (clearedSystemTailHouse t D + clearedSystemMatrixHouse U D) * C^n :=
            clearedPolynomialSystem_conjugate_step t U Z ht0 D htdeg hUdeg hode
              σ C hC n hprev i j
          _ ≤ C * C^n := by
            apply mul_le_mul_of_nonneg_right _ (pow_nonneg (le_trans zero_le_one hC) n)
            dsimp only [C, clearedSystemHouseConstant]
            linarith
          _ = C^(n+1) := by rw [pow_succ]; ring
  intro m i j
  exact (NumberField.canonicalEmbedding.norm_le_iff _ _).2 (fun σ => hb σ m i j)

/-- A finite polynomial matrix has an internally constructed common degree. -/
theorem exists_clearedSystem_common_degree {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) :
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
house bound, simultaneously for every coefficient and every complex embedding.
The point and the original clearing data are retained literally. -/
theorem ordinaryPoint_fundamental_house_bound {r : ℕ}
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (hα : t.eval α ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m i j,
      NumberField.house (PowerSeries.coeff K m
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j)) ≤ C^m := by
  let tα := ordinaryPointPolynomialShift α t
  let Uα : Matrix (Fin r) (Fin r) (Polynomial K) :=
    fun i l => ordinaryPointPolynomialShift α (U i l)
  let Z := formalFundamentalMatrix (ordinaryPointClearedMatrix t U α)
  obtain ⟨D,htdeg,hUdeg⟩ := exists_clearedSystem_common_degree tα Uα
  have h0 : tα.coeff 0 = t.eval α := ordinaryPointPolynomialSeries_constantCoeff α t
  have ht0 : tα.coeff 0 ≠ 0 := by rw [h0]; exact hα
  have hode : ∀ i j, (tα : PowerSeries K) * PowerSeries.derivative K (Z i j) =
      ∑ l, (Uα i l : PowerSeries K) * Z l j :=
    ordinaryPointClearedMatrix_fundamental_cleared t U α hα
  refine ⟨clearedSystemHouseConstant tα Uα D,
    clearedSystemHouseConstant_one_le tα Uα D,?_⟩
  exact clearedPolynomialSystem_coeff_house_bound tα Uα Z ht0 D htdeg hUdeg hode
    (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))

end StrictEUnit
end
