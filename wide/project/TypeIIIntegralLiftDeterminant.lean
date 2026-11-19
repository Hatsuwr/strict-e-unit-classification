import TypeIIIntegralLiftHouse
import IntegralNormHouse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Source-only bounds for the determinant of the SAME explicit lift matrix.
Nonvanishing of its chosen coefficient is explicit, not derived from Padé. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

theorem polynomial_finset_product_house
    {K I : Type*} [Field K] [NumberField K] [DecidableEq I]
    (S : Finset I) (P : I → Polynomial (𝓞 K)) (d : ℕ) (E : ℝ) (hE : 0 ≤ E)
    (hd : ∀ i ∈ S, (P i).natDegree ≤ d)
    (hP : ∀ i ∈ S, ∀ n, NumberField.house ((P i).coeff n : K) ≤ E) :
    ∀ n, NumberField.house ((∏ i ∈ S, P i).coeff n : K) ≤ ((d+1)*E)^S.card := by
  revert hd hP
  induction S using Finset.induction_on with
  | empty =>
      intro hd hP n
      by_cases hn : n=0
      · subst n; simp [NumberField.house]
      · simp [Polynomial.coeff_one, hn, NumberField.house]
  | @insert i S hi ih =>
      intro hd hP n
      rw [Finset.prod_insert hi, Finset.card_insert_of_not_mem hi, pow_succ']
      have htail := ih (fun a ha => hd a (Finset.mem_insert_of_mem ha))
        (fun a ha => hP a (Finset.mem_insert_of_mem ha))
      have h := typeII_polynomial_product_house (P i) (∏ a ∈ S, P a) d
        (hd i (Finset.mem_insert_self _ _)) E (((d+1)*E)^S.card)
        hE (pow_nonneg (mul_nonneg (by positivity) hE) _)
        (hP i (Finset.mem_insert_self _ _)) htail n
      simpa only [mul_assoc] using h

/-- An explicit coefficient bound for one determinant, including rank zero. -/
theorem integral_polynomial_matrix_det_house
    {K : Type*} [Field K] [NumberField K] (r d : ℕ)
    (M : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ) (hE : 0 ≤ E)
    (hd : ∀ i j, (M i j).natDegree ≤ d)
    (hM : ∀ i j n, NumberField.house ((M i j).coeff n : K) ≤ E) (n : ℕ) :
    NumberField.house (M.det.coeff n : K) ≤ (r.factorial : ℝ)*((d+1)*E)^r := by
  classical
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  change NumberField.house (φ (M.det.coeff n)) ≤ _
  rw [Matrix.det_apply, Polynomial.finset_sum_coeff, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin r), NumberField.house
        (φ ((Equiv.Perm.sign σ • ∏ i, M (σ i) i).coeff n)) :=
      NumberField.house_sum_le_sum_house _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), ((d+1)*E)^r := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hp := polynomial_finset_product_house Finset.univ (fun i => M (σ i) i)
        d E hE (fun i _ => hd (σ i) i) (fun i _ => hM (σ i) i) n
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · simpa [hs, φ] using hp
      · simpa [hs, φ, NumberField.house] using hp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm,
        Fintype.card_fin, nsmul_eq_mul]

/-- Literal first-r-column matrix, not a chosen bounded replacement. -/
def typeIIIntegralLiftMatrix {R : Type*} [CommRing R] (r N τ : ℕ)
    (T Q : Polynomial R) (b : Fin r → ℕ → R) :
    Matrix (Fin r) (Fin r) (Polynomial R) :=
  Matrix.of fun i j => typeIIIntegralLift T Q (b i) (N+j.val*τ) j.val

/-- Sum of the actual first-r individual column bounds. This explicit
nonnegative quantity also covers r=0 without an arbitrary maximum choice. -/
def typeIIIntegralLiftMatrixBound (r e N : ℕ) (HT HQ Hb : ℝ) : ℝ :=
  ∑ j : Fin r, (j.val*e+1)*(((e+1)*HT)^j.val)*((N+1)*(2:ℝ)^N*HQ*Hb)

theorem typeIIIntegralLiftMatrix_det_house
    {K : Type*} [Field K] [NumberField K]
    (r e N τ M : ℕ) (T Q : Polynomial (𝓞 K)) (b : Fin r → ℕ → 𝓞 K)
    (hTdeg : T.natDegree ≤ e) (hQdeg : Q.natDegree ≤ N)
    (HT HQ Hb : ℝ) (hHT : 0 ≤ HT) (hHQ : 0 ≤ HQ) (hHb : 0 ≤ Hb)
    (hT : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hQ : ∀ n, NumberField.house (Q.coeff n : K) ≤ HQ)
    (hb : ∀ i n, n ≤ N+M → NumberField.house (b i n : K) ≤ Hb)
    (hcut : (r-1)*τ ≤ M) (n : ℕ) :
    NumberField.house ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff n : K) ≤
      (r.factorial : ℝ)*(((N+(r-1)*τ : ℕ)+1 : ℝ)*
        typeIIIntegralLiftMatrixBound r e N HT HQ Hb)^r := by
  classical
  let E := typeIIIntegralLiftMatrixBound r e N HT HQ Hb
  have hE : 0 ≤ E := by
    unfold E typeIIIntegralLiftMatrixBound
    apply Finset.sum_nonneg
    intro j hj
    positivity
  apply integral_polynomial_matrix_det_house r (N+(r-1)*τ) _ E hE
  · intro i j
    have h := PowerSeries.natDegree_trunc_lt
      (((T^j.val*Polynomial.hasseDeriv j.val Q : Polynomial (𝓞 K)) :
        PowerSeries (𝓞 K))*PowerSeries.mk (b i)) (N+j.val*τ)
    change (PowerSeries.trunc (N+j.val*τ+1) _).natDegree ≤ _
    have hj : j.val ≤ r-1 := by omega
    exact (Nat.le_of_lt_succ h).trans (Nat.add_le_add_left (Nat.mul_le_mul_right τ hj) N)
  · intro i j k
    have hj : j.val ≤ r-1 := by omega
    have hdeg : N+j.val*τ ≤ N+M :=
      Nat.add_le_add_left ((Nat.mul_le_mul_right τ hj).trans hcut) N
    have h := typeIIIntegralLift_house T Q (b i) e N (N+j.val*τ) j.val
      hTdeg hQdeg HT HQ Hb hHT hHQ hHb hT hQ
      (fun m hm => hb i m (hm.trans hdeg)) k
    apply h.trans
    exact Finset.single_le_sum
      (f := fun a : Fin r => (a.val*e+1)*(((e+1)*HT)^a.val)*((N+1)*(2:ℝ)^N*HQ*Hb))
      (fun a _ => by positivity) (Finset.mem_univ j)

/-- ONE fixed coefficient norm: positive and explicitly bounded. This is not
an assertion that the determinant is nonzero; hk remains a real rank gap. -/
theorem typeIIIntegralLiftMatrix_coefficient_norm_bound
    {K : Type*} [Field K] [NumberField K]
    (r e N τ M : ℕ) (T Q : Polynomial (𝓞 K)) (b : Fin r → ℕ → 𝓞 K)
    (hTdeg : T.natDegree ≤ e) (hQdeg : Q.natDegree ≤ N)
    (HT HQ Hb : ℝ) (hHT : 0 ≤ HT) (hHQ : 0 ≤ HQ) (hHb : 0 ≤ Hb)
    (hT : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hQ : ∀ n, NumberField.house (Q.coeff n : K) ≤ HQ)
    (hb : ∀ i n, n ≤ N+M → NumberField.house (b i n : K) ≤ Hb)
    (hcut : (r-1)*τ ≤ M) (k : ℕ)
    (hk : (typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k ≠ 0) :
    0 < Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k)) ∧
    (Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k)) : ℝ) ≤
      ((r.factorial : ℝ)*(((N+(r-1)*τ : ℕ)+1 : ℝ)*
        typeIIIntegralLiftMatrixBound r e N HT HQ Hb)^r)^Module.finrank ℚ K := by
  obtain ⟨hpos, hbound, c, hc⟩ := ringOfIntegers_natAbs_norm_certificate
    ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k) hk
  refine ⟨hpos, hbound.trans ?_⟩
  exact pow_le_pow_left₀ (NumberField.house_nonneg _)
    (typeIIIntegralLiftMatrix_det_house r e N τ M T Q b hTdeg hQdeg
      HT HQ Hb hHT hHQ hHb hT hQ hb hcut k) _

end StrictEUnit
end
