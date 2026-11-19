import BalancedIntegralTypeIIPade
import TypeIIUniformAnnihilatorRank
import TypeIILiteralLiftRank
import TypeIISameMatrixExponential

/-! SAME arithmetic certificate and approximants. Uniform annihilator degree
remains explicit, but joint rank/size existence is proved, not assumed. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- Constants B,Z precede s. The balanced approximation is destructured once;
its SAME Q/P/delta/b supplies both the House bound and the full-rank literal lift. -/
theorem exists_typeII_joint_arithmetic_witnesses
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (τ D : ℕ)
    (hD : UniformPolynomialDualAnnihilator r stage14_rationalOrdinaryDerivation A D)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (C : ℝ) (hC : 1 ≤ C) (δ : ℕ → ℕ) (hδ : ∀ L, 0 < δ L)
    (hδbound : ∀ L, (δ L : ℝ) ≤ C^(L+1))
    (b : ℕ → Fin r → ℕ → 𝓞 K)
    (hb : ∀ L i n, n ≤ L → (b L i n : K) = (δ L : K)*PowerSeries.coeff K n (f i))
    (hhouse : ∀ L i n, n ≤ L → NumberField.house (b L i n : K) ≤ C^(2*(L+1))) :
    ∃ B : ℝ, 1 ≤ B ∧ ∃ Z : ℕ, 0 < Z ∧
      ∀ s, Nonempty (TypeIIJointExponentialWitness K r T U A f τ Z s B C) := by
  classical
  obtain ⟨Z,hZ,hrank⟩ := typeII_rank_of_uniform_polynomial_annihilator hr A f hli D hD
  obtain ⟨B,hB,happrox⟩ := exists_exponential_integral_typeII_pade K r hr f C hC δ hδ hδbound b hb hhouse
  refine ⟨B,hB,Z,hZ,?_⟩
  intro s
  let t := (r*(τ+1)+Z+1)*(s+1)
  let N := 2*r*t-1
  let L := N+t
  have hparam := typeII_affine_cutoff r τ Z s hr
  change 0 < t ∧ Z < t ∧ (s+r-1)*(τ+1) ≤ t at hparam
  obtain ⟨Q,P,hQ,hQN,hPN,htrunc,hcontact,hQH,hPH⟩ := happrox t hparam.1
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let PK : Fin r → Polynomial K := fun i => (P i).map φ
  have hQK : Q.map φ ≠ 0 := by
    intro hz
    apply hQ
    apply Polynomial.map_injective φ NumberField.RingOfIntegers.coe_injective
    simpa only [Polynomial.map_zero] using hz
  have hQKN : (Q.map φ).natDegree ≤ N := Polynomial.natDegree_map_le.trans hQN
  have hPKN (i : Fin r) : (PK i).natDegree ≤ N := Polynomial.natDegree_map_le.trans (hPN i)
  have hdim : N+1 = 2*r*t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) hparam.1))
  have hlength : N+t+1 = (2*r+1)*t := by
    calc N+t+1 = (N+1)+t := by omega
         _ = _ := by rw [hdim]; ring
  have hc (i : Fin r) : seriesContact (N+t+1)
      ((Q.map φ : PowerSeries K)*f i-(PK i : PowerSeries K)) := by
    intro n hn
    apply hcontact i n
    rwa [hlength] at hn
  have hraw := hrank N t (Nat.le_of_lt hparam.2.1) (Q.map φ) hQK hQKN PK hc
  have hcut : (r-1)*(τ+1) ≤ t :=
    (Nat.mul_le_mul_right (τ+1) (show r-1 ≤ s+r-1 by omega)).trans hparam.2.2
  obtain ⟨hdet,k,hk⟩ := typeII_literal_lift_det_and_coefficient_ne_zero
    T Q U PK A f (b L) (δ L) (hδ L) N t τ hT0 hT hU hPKN hclear hf hc
      (hb L) hcut hraw
  refine ⟨{
    Q := Q
    P := PK
    b := b L
    δ := δ L
    delta_pos := hδ L
    q_nonzero := hQ
    q_degree := hQN
    p_degree := hPKN
    contact := hc
    «prefix» := hb L
    q_house := hQH
    prefix_house := hhouse L
    coefficient_index := k
    rank_coefficient := hk
  }⟩

/-- One exponential base before the cutoff, with one positive integer clearing
ALL connection-polynomial coefficients through that cutoff. No supplied joint
witness or independent rank witness remains; uniformD and arithmetic remain. -/
theorem exists_typeII_arithmetic_exponential_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (e τ D : ℕ) (HT C : ℝ) (hHT : 1 ≤ HT) (hC : 1 ≤ C)
    (hD : UniformPolynomialDualAnnihilator r stage14_rationalOrdinaryDerivation A D)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ) (hTe : T.natDegree ≤ e)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (δ : ℕ → ℕ) (hδ : ∀ L, 0 < δ L)
    (hδbound : ∀ L, (δ L : ℝ) ≤ C^(L+1))
    (b : ℕ → Fin r → ℕ → 𝓞 K)
    (hb : ∀ L i n, n ≤ L → (b L i n : K) = (δ L : K)*PowerSeries.coeff K n (f i))
    (hhouse : ∀ L i n, n ≤ L → NumberField.house (b L i n : K) ≤ C^(2*(L+1))) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ E^(s+1) ∧
      ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((q:K)*
          (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  obtain ⟨B,hB,Z,hZ,hJoint⟩ := exists_typeII_joint_arithmetic_witnesses hr T U A f τ D
    hD hli hT0 hT hU hclear hf C hC δ hδ hδbound b hb hhouse
  exact exists_typeII_same_matrix_exponential_denominators hr T U A f e τ Z HT B C
    hHT hB hC hT0 hT hU hTe hTH hclear hf hJoint

end StrictEUnit
end
