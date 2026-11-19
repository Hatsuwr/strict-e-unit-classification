import RationalCovariantJetInterpolation
import RelationQuotientCyclicRank
import PrescribedComplementBasis
import RegularCompletedRowCoordinates

/-! New proof reconstruction, not recovered historical source.
A prescribed row outside the specialized relation span is completed to a basis.
Polynomial covariant jet interpolation realizes that complement. The completed
matrix has a power-series inverse, which supplies regular rational recurrence
coefficients for the same original rational system and ordinary point. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Construct a polynomial row with the prescribed value, a full independent
image prefix, and a recurrence whose coefficients are regular at the specified
ordinary point. The relation kernel and its independent specialization are the
only relation hypotheses; no cyclicity or recurrence is assumed. -/
theorem exists_prescribed_polynomial_regular_cyclic_row
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V]
    [Module (RatFunc K) V] {r s : ℕ}
    (α : K) (F : (Fin r → RatFunc K) →ₗ[RatFunc K] V)
    (A : Fin r → Fin r → RatFunc K)
    (t : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (B : Fin s → Fin r → Polynomial K)
    (hker : LinearMap.ker F = Submodule.span (RatFunc K)
      (Set.range (fun i j => algebraMap (Polynomial K) (RatFunc K) (B i j))))
    (hB : LinearIndependent K (fun i j => (B i j).eval α))
    (c : Fin r → K)
    (hc : c ∉ Submodule.span K (Set.range (fun i j => (B i j).eval α))) :
    ∃ m : ℕ, 0 < m ∧ m + s = r ∧ ∃ p : Fin r → Polynomial K,
      (∀ j, (p j).eval α = c j) ∧
      LinearIndependent (RatFunc K) (fun i : Fin m =>
        F ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[i.val]
          (fun j => algebraMap (Polynomial K) (RatFunc K) (p j)))) ∧
      ∃ b : Fin m → RatFunc K, ∃ bS : Fin m → PowerSeries K,
        (∑ i, b i •
          F ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[i.val]
            (fun j => algebraMap (Polynomial K) (RatFunc K) (p j)))) =
          F ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[m]
            (fun j => algebraMap (Polynomial K) (RatFunc K) (p j))) ∧
        ∀ i, HahnSeries.ofPowerSeries ℤ K (bS i) =
          ordinaryPointRationalMap α (b i) := by
  classical
  let B₀ : Fin s → Fin r → K := fun i j => (B i j).eval α
  obtain ⟨m, hm, v, hv0, hvli, _hvspan, hvdim⟩ :=
    exists_prescribed_complement_family hB hc
  have hdim : m + s = r := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hvdim
  let e : (Fin m ⊕ Fin s) ≃ Fin r := Fintype.equivOfCardEq (by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hdim)
  let jets : ℕ → Fin r → K := fun n => if hn : n < m then v ⟨n, hn⟩ else 0
  obtain ⟨p, hp0, hpjet⟩ := exists_polynomial_rational_covariant_jets_with_value
    α A t U hα hclear jets m hm
  have hp : ∀ j, (p j).eval α = c j := by
    intro j
    rw [hp0]
    change (if hn : 0 < m then v ⟨0, hn⟩ else 0) j = c j
    rw [dif_pos hm]
    exact congrFun hv0 j
  let q : Fin r → RatFunc K :=
    fun j => algebraMap (Polynomial K) (RatFunc K) (p j)
  let Q : ℕ → Fin r → RatFunc K :=
    fun n => (rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[n] q
  let M : Fin r → Fin r → PowerSeries K := fun i j =>
    ordinaryPointPolynomialSeries α (U i j) * (ordinaryPointPolynomialSeries α t)⁻¹
  have hM : ∀ i j, HahnSeries.ofPowerSeries ℤ K (M i j) =
      ordinaryPointRationalMap α (A i j) := by
    intro i j
    exact (ordinaryPointRationalMap_of_clearing α (A i j) t (U i j)
      hα (hclear i j)).symm
  let pS : Fin r → PowerSeries K := fun j => ordinaryPointPolynomialSeries α (p j)
  let QS : ℕ → Fin r → PowerSeries K := fun n => (ordinaryCovariantRow M)^[n] pS
  have hpS : ∀ j, HahnSeries.ofPowerSeries ℤ K (pS j) =
      ordinaryPointRationalMap α (q j) := by
    intro j
    rw [ordinaryPointRationalMap_polynomial, ordinaryPointPolynomialSeries_coe]
  have hQ : ∀ n j, HahnSeries.ofPowerSeries ℤ K (QS n j) =
      ordinaryPointRationalMap α (Q n j) := by
    intro n
    exact rationalCovariantRow_local_series_iterate α A M hM q pS hpS n
  have hQS0 : ∀ (i : Fin m) j, PowerSeries.constantCoeff K (QS i.val j) = v i j := by
    intro i j
    have hjet : (ordinaryPointRationalMap α (Q i.val j)).coeff 0 = v i j := by
      simpa only [jets, dif_pos i.isLt] using hpjet i.val i.isLt j
    rw [← hQ] at hjet
    have hcoeff : PowerSeries.constantCoeff K (QS i.val j) =
        (HahnSeries.ofPowerSeries ℤ K (QS i.val j)).coeff (0 : ℤ) := by
      simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff] using
        (HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) (QS i.val j) 0).symm
    exact hcoeff.trans hjet
  let BR : Fin s → Fin r → RatFunc K :=
    fun i j => algebraMap (Polynomial K) (RatFunc K) (B i j)
  let BS : Fin s → Fin r → PowerSeries K :=
    fun i j => ordinaryPointPolynomialSeries α (B i j)
  have hBS : ∀ i j, HahnSeries.ofPowerSeries ℤ K (BS i j) =
      ordinaryPointRationalMap α (BR i j) := by
    intro i j
    rw [ordinaryPointRationalMap_polynomial, ordinaryPointPolynomialSeries_coe]
  let H : Matrix (Fin r) (Fin r) (RatFunc K) :=
    fun k => Sum.elim (fun i : Fin m => Q i.val) BR (e.symm k)
  let HS : Matrix (Fin r) (Fin r) (PowerSeries K) :=
    fun k => Sum.elim (fun i : Fin m => QS i.val) BS (e.symm k)
  let H₀ : Matrix (Fin r) (Fin r) K := fun k => Sum.elim v B₀ (e.symm k)
  have hHmap : HS.map (HahnSeries.ofPowerSeries ℤ K) =
      H.map (ordinaryPointRationalMap α) := by
    apply Matrix.ext
    intro k j
    change HahnSeries.ofPowerSeries ℤ K
      (Sum.elim (fun i : Fin m => QS i.val) BS (e.symm k) j) =
      ordinaryPointRationalMap α
        (Sum.elim (fun i : Fin m => Q i.val) BR (e.symm k) j)
    cases e.symm k with
    | inl i => exact hQ i.val j
    | inr i => exact hBS i j
  have hH0 : HS.map (PowerSeries.constantCoeff K) = H₀ := by
    ext k j
    change PowerSeries.constantCoeff K
      (Sum.elim (fun i : Fin m => QS i.val) BS (e.symm k) j) =
      Sum.elim v B₀ (e.symm k) j
    cases e.symm k with
    | inl i => exact hQS0 i j
    | inr i => exact ordinaryPointPolynomialSeries_constantCoeff α (B i j)
  have hH0li : LinearIndependent K H₀.row := hvli.comp e.symm e.symm.injective
  have hH0unit : IsUnit H₀ := Matrix.linearIndependent_rows_iff_isUnit.mp hH0li
  have hHSunit : IsUnit HS.det := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [(PowerSeries.constantCoeff K).map_det]
    change IsUnit (HS.map (PowerSeries.constantCoeff K)).det
    rw [hH0]
    exact (Matrix.isUnit_iff_isUnit_det H₀).mp hH0unit
  obtain ⟨hHdet, x, xS, hx, hxreg⟩ := matrix_regular_row_coordinates
    (ordinaryPointRationalMap α) (HahnSeries.ofPowerSeries ℤ K)
    H HS hHmap hHSunit (Q m) (QS m) (hQ m)
  have hrows : LinearIndependent (RatFunc K) H.row :=
    Matrix.linearIndependent_rows_of_det_ne_zero hHdet
  have hfull : LinearIndependent (RatFunc K)
      (Sum.elim (fun i : Fin m => Q i.val) BR) := by
    have heq : H.row ∘ e = Sum.elim (fun i : Fin m => Q i.val) BR := by
      funext i
      simp only [Function.comp_apply, Matrix.row_def, H, e.symm_apply_apply]
    rw [← heq]
    exact hrows.comp e e.injective
  have hqli : LinearIndependent (RatFunc K)
      (fun i : Fin m => (LinearMap.ker F).mkQ (Q i.val)) :=
    quotient_independent_of_completed (LinearMap.ker F)
      (fun i : Fin m => Q i.val) BR hker hfull
  have hli : LinearIndependent (RatFunc K) (fun i : Fin m => F (Q i.val)) :=
    (linearIndependent_relationQuotient_iff F (fun i : Fin m => Q i.val)).mp hqli
  have hBR : ∀ i, F (BR i) = 0 := by
    intro i
    apply LinearMap.mem_ker.mp
    rw [hker]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hsum : (∑ k, x k • H k) = Q m := by
    funext j
    have hj := congrFun hx j
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.vecMul, dotProduct] using hj
  have hsum' : (∑ i : Fin m ⊕ Fin s,
      x (e i) • Sum.elim (fun i : Fin m => Q i.val) BR i) = Q m := by
    calc
      _ = ∑ k : Fin r, x k • H k := by
        simpa only [H, e.symm_apply_apply] using
          e.sum_comp (fun k : Fin r => x k • H k)
      _ = Q m := hsum
  have hrec : (∑ i : Fin m, x (e (Sum.inl i)) • F (Q i.val)) = F (Q m) := by
    have hf := congrArg F hsum'
    simpa only [map_add, map_sum, map_smul, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, hBR, smul_zero, Finset.sum_const_zero,
      add_zero] using hf
  exact ⟨m, hm, hdim, p, hp, hli, fun i => x (e (Sum.inl i)),
    fun i => xS (e (Sum.inl i)), hrec, fun i => hxreg (e (Sum.inl i))⟩

end StrictEUnit
