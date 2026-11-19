import TypeIIJointArithmeticAssembly
import UniformPolynomialDualAnnihilatorExistence
import V5TypeIICutoffHeight
import V5FactorialCutoffRescale

noncomputable section
namespace StrictEUnit
open scoped BigOperators NumberField Matrix

/-- Arbitrarily small factorial-power growth of a common integral prefix.
The certificate may depend on the requested precision. -/
def V5BroadIntegralPrefix (K : Type*) [Field K] [NumberField K]
    {r : ℕ} (f : Fin r → PowerSeries K) : Prop :=
  ∀ prec : ℕ, ∃ C : ℝ, 1 ≤ C ∧
    ∃ (δ : ℕ → ℕ) (b : ℕ → Fin r → ℕ → 𝓞 K) (H : ℕ → ℝ),
      (∀ L, 0 < δ L) ∧ (∀ L, 1 ≤ H L) ∧ (∀ L, (δ L : ℝ) ≤ H L) ∧
      (∀ L i n, n ≤ L → (b L i n : K) = (δ L : K)*PowerSeries.coeff K n (f i)) ∧
      (∀ L i n, n ≤ L → NumberField.house (b L i n : K) ≤ H L) ∧
      ∀ L, H L^prec ≤ C^(L+1)*(L.factorial : ℝ)

/-- Broad prefix arithmetic yields a single positive norm denominator for
all connection coefficients up to a cutoff, with squared factorial growth. -/
theorem v5_broad_same_matrix_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (e τ : ℕ) (HT : ℝ) (hHT : 1 ≤ HT)
    (hli : LinearIndependent (RatFunc K) (fun i => HahnSeries.ofPowerSeries ℤ K (f i)))
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ) (hTe : T.natDegree ≤ e)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hprefix : V5BroadIntegralPrefix K f) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ q : ℕ, 0 < q ∧
      (q : ℝ)^2 ≤ E^(s+1)*(s.factorial : ℝ) ∧
      ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((q : K)*
          (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  classical
  obtain ⟨D, hD⟩ := exists_uniform_polynomial_dual_annihilator A
  obtain ⟨Z,hZ,hrank⟩ := typeII_rank_of_uniform_polynomial_annihilator hr A f hli D hD
  obtain ⟨B,hB,happrox⟩ := v5_exists_cutoff_height_typeII_pade K r hr
  let J := r*(τ+1)+Z+1
  let lam := (2*r+1)*J
  let d := Module.finrank ℚ K
  have hlam : 0 < lam := Nat.mul_pos (by omega) (by dsimp [J]; omega)
  obtain ⟨C,hC,δ,b,H,hδ,hH,hδH,hb,hh,hpow⟩ := hprefix (lam*(6*r*d))
  let G := typeIIDeterminantExponentialBase r e τ HT B 1
  have hG : 1 ≤ G :=
    (v5_typeII_determinant_bound_cutoff_height r e τ 1 HT B 1 hr (by decide) hHT hB le_rfl).1
  let E₀ := 2*C*(lam : ℝ)
  have hE₀ : 1 ≤ E₀ := by
    have hl : (1 : ℝ) ≤ lam := by exact_mod_cast hlam
    dsimp [E₀]
    nlinarith
  refine ⟨G^(2*d*J)*E₀, one_le_mul_of_one_le_of_one_le (one_le_pow₀ hG) hE₀, ?_⟩
  intro s
  let t := J*(s+1)
  let N := 2*r*t-1
  let L := N+t
  have hparam := typeII_affine_cutoff r τ Z s hr
  change 0 < t ∧ Z < t ∧ (s+r-1)*(τ+1) ≤ t at hparam
  obtain ⟨Q,P,hQ,hQN,hPN,hcontact,hQH⟩ :=
    happrox t (δ L) f (b L) (H L) hparam.1 (hδ L) (hH L) (hδH L) (hb L) (hh L)
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let PK : Fin r → Polynomial K := fun i => (P i).map φ
  have hQK : Q.map φ ≠ 0 := by
    intro hz
    apply hQ
    apply Polynomial.map_injective φ NumberField.RingOfIntegers.coe_injective
    simpa only [Polynomial.map_zero] using hz
  have hQKN : (Q.map φ).natDegree ≤ N := Polynomial.natDegree_map_le.trans hQN
  have hPKN (i : Fin r) : (PK i).natDegree ≤ N := Polynomial.natDegree_map_le.trans (hPN i)
  have hc (i : Fin r) : seriesContact (N+t+1)
      ((Q.map φ : PowerSeries K)*f i-(PK i : PowerSeries K)) := hcontact i
  have hraw := hrank N t (Nat.le_of_lt hparam.2.1) (Q.map φ) hQK hQKN PK hc
  have hcut : (r-1)*(τ+1) ≤ t :=
    (Nat.mul_le_mul_right (τ+1) (show r-1 ≤ s+r-1 by omega)).trans hparam.2.2
  obtain ⟨hdet,k,hk⟩ := typeII_literal_lift_det_and_coefficient_ne_zero
    T Q U PK A f (b L) (δ L) (hδ L) N t τ hT0 hT hU hPKN hclear hf hc
      (hb L) hcut hraw
  obtain ⟨hpos,hbound,hint⟩ := typeII_same_matrix_positive_denominator
    T Q U PK A f (b L) (δ L : K) N t τ s hT0 hT hU hPKN hclear hf hc (hb L)
    hparam.2.2 e hTe hQN HT (B^t*(H L)^2) (H L)
    (zero_le_one.trans hHT) (by positivity) (zero_le_one.trans (hH L)) hTH hQH (hh L) k hk
  refine ⟨_, hpos, ?_, hint⟩
  obtain ⟨_,hdetbound⟩ := v5_typeII_determinant_bound_cutoff_height
    r e τ t HT B (H L) hr hparam.1 hHT hB (hH L)
  have hHL : 0 ≤ H L := zero_le_one.trans (hH L)
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hHT0 : 0 ≤ HT := zero_le_one.trans hHT
  have hnonneg : 0 ≤ (r.factorial : ℝ)*(((N+(r-1)*τ : ℕ)+1 : ℝ)*
      typeIIIntegralLiftMatrixBound r e N HT (B^t*(H L)^2) (H L))^r := by
    unfold typeIIIntegralLiftMatrixBound
    positivity
  have hqb := hbound.trans (pow_le_pow_left₀ hnonneg hdetbound d)
  have hsq := pow_le_pow_left₀ (Nat.cast_nonneg _) hqb 2
  have hsq' : (↑(Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q (b L)).det.coeff k))) : ℝ)^2 ≤
      G^(2*d*t)*(H L)^(6*r*d) := by
    convert hsq using 1
    simp only [mul_pow, ← pow_mul]
    congr 1 <;> ring
  have hdim : N+1 = 2*r*t := Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Nat.mul_pos (Nat.mul_pos (by decide) hr) hparam.1))
  have hL : L = lam*(s+1)-1 := by
    have hlen : L+1 = lam*(s+1) := by
      dsimp [L]
      calc N+t+1 = (N+1)+t := by omega
           _ = _ := by rw [hdim]; dsimp [t,lam]; ring
    omega
  have hres : (H L)^(6*r*d) ≤ E₀^(s+1)*(s.factorial : ℝ) := by
    rw [hL]
    exact v5_factorial_cutoff_rescale H C lam (6*r*d) hlam hC hpow s
  calc
    _ ≤ G^(2*d*t)*(H L)^(6*r*d) := hsq'
    _ ≤ G^(2*d*t)*(E₀^(s+1)*(s.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hres (pow_nonneg (zero_le_one.trans hG) _)
    _ = _ := by
      simp only [mul_pow, ← pow_mul]
      rw [show 2*d*t = (2*d*J)*(s+1) by dsimp [t]; ring]
      ring

#print axioms v5_broad_same_matrix_denominators
end StrictEUnit
end
