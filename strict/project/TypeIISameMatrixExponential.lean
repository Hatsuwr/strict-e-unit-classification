import TypeIIExponentialDenominatorBounds

/-! The rank premise is for THIS bounded approximation, not an unrelated witness.
The fixed exponential base contains no cutoff or chosen approximation data.
Raw-column rank transfer is not asserted here: hk is the exact literal lift
coefficient. Positivity of delta must be retained when proving that transfer. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

theorem typeII_same_matrix_exponential_denominator
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T Q : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → 𝓞 K) (δ : K)
    (N M τ s Z t : ℕ) (hr : 0 < r)
    (ht : t = (r*(τ+1)+Z+1)*(s+1))
    (hN : N = 2*r*t-1) (hM : M = t)
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → (b i n : K) = δ * PowerSeries.coeff K n (f i))
    (e : ℕ) (hTe : T.natDegree ≤ e) (hQN : Q.natDegree ≤ N)
    (HT B C : ℝ) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hQH : ∀ n, NumberField.house (Q.coeff n : K) ≤ B^t)
    (hbH : ∀ i n, n ≤ N+M → NumberField.house (b i n : K) ≤ C^(2*(N+M+1)))
    (k : ℕ) (hk : (typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k ≠ 0) :
    let q := Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k))
    0 < q ∧
    (q : ℝ) ≤
      ((typeIIDeterminantExponentialBase r e τ HT B C)^
        (Module.finrank ℚ K*(r*(τ+1)+Z+1)))^(s+1) ∧
    ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
      IsIntegral ℤ ((q : K)*
        (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  have hp := typeII_affine_cutoff r τ Z s hr
  dsimp only at hp
  have htpos : 0 < t := by simpa only [ht] using hp.1
  have hcut : (s+r-1)*(τ+1) ≤ M := by rw [hM,ht]; exact hp.2.2
  obtain ⟨hpos,hbound,hint⟩ := typeII_same_matrix_positive_denominator
    T Q U P A f b δ N M τ s hT0 hT hU hP hclear hf hcontact hb hcut
    e hTe hQN HT (B^t) (C^(2*(N+M+1)))
    (zero_le_one.trans hHT) (pow_nonneg (zero_le_one.trans hB) _)
    (pow_nonneg (zero_le_one.trans hC) _) hTH hQH hbH k hk
  refine ⟨hpos,hbound.trans ?_,hint⟩
  obtain ⟨hG,hdet⟩ := typeII_determinant_bound_exponential r e τ t HT B C
    hr htpos hHT hB hC
  subst N
  subst M
  have hnonneg : 0 ≤ (r.factorial:ℝ)*(((2*r*t-1+(r-1)*τ:ℕ)+1:ℝ)*
      typeIIIntegralLiftMatrixBound r e (2*r*t-1) HT (B^t)
        (C^(2*((2*r*t-1)+t+1))))^r := by
    unfold typeIIIntegralLiftMatrixBound
    positivity
  calc
    _ ≤ ((typeIIDeterminantExponentialBase r e τ HT B C)^t)^Module.finrank ℚ K :=
      pow_le_pow_left₀ hnonneg hdet _
    _ = _ := by rw [ht]; simp only [← pow_mul]; congr 1; ring

/-- A JOINT witness for the very same small approximation and literal full-rank
lift. This structure is not asserted inhabited: rank remains the missing input.
Delta is positive for the eventual raw-rank transfer, which is NOT proved here. -/
structure TypeIIJointExponentialWitness
    (K : Type*) [Field K] [NumberField K] (r : ℕ)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (τ Z s : ℕ) (B C : ℝ) where
  Q : Polynomial (𝓞 K)
  P : Fin r → Polynomial K
  b : Fin r → ℕ → 𝓞 K
  δ : ℕ
  delta_pos : 0 < δ
  q_nonzero : Q ≠ 0
  q_degree : Q.natDegree ≤ 2*r*((r*(τ+1)+Z+1)*(s+1))-1
  p_degree : ∀ i, (P i).natDegree ≤ 2*r*((r*(τ+1)+Z+1)*(s+1))-1
  contact : ∀ i, seriesContact
    ((2*r*((r*(τ+1)+Z+1)*(s+1))-1)+((r*(τ+1)+Z+1)*(s+1))+1)
    ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f i-(P i : PowerSeries K))
  «prefix» : ∀ i n,
    n ≤ (2*r*((r*(τ+1)+Z+1)*(s+1))-1)+((r*(τ+1)+Z+1)*(s+1)) →
    (b i n : K) = (δ:K)*PowerSeries.coeff K n (f i)
  q_house : ∀ n, NumberField.house (Q.coeff n : K) ≤ B^((r*(τ+1)+Z+1)*(s+1))
  prefix_house : ∀ i n,
    n ≤ (2*r*((r*(τ+1)+Z+1)*(s+1))-1)+((r*(τ+1)+Z+1)*(s+1)) →
    NumberField.house (b i n : K) ≤
      C^(2*((2*r*((r*(τ+1)+Z+1)*(s+1))-1)+((r*(τ+1)+Z+1)*(s+1))+1))
  coefficient_index : ℕ
  rank_coefficient : (typeIIIntegralLiftMatrix r
    (2*r*((r*(τ+1)+Z+1)*(s+1))-1) τ T Q b).det.coeff coefficient_index ≠ 0

/-- ONE fixed exponential base before s, ONE norm denominator for all n≤s.
The only witness-selection hypothesis is JOINT: bounded approximation and rank
are carried by the same Q/P/b/delta. No independent rank witness is selected. -/
theorem exists_typeII_same_matrix_exponential_denominators
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (hr : 0 < r)
    (T : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (f : Fin r → PowerSeries K)
    (e τ Z : ℕ) (HT B C : ℝ) (hHT : 1 ≤ HT) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ) (hTe : T.natDegree ≤ e)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hJoint : ∀ s, Nonempty (TypeIIJointExponentialWitness K r T U A f τ Z s B C)) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ s : ℕ, ∃ q : ℕ, 0 < q ∧ (q:ℝ) ≤ E^(s+1) ∧
      ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
        IsIntegral ℤ ((q:K)*
          (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  let G := typeIIDeterminantExponentialBase r e τ HT B C
  have hG : 1 ≤ G :=
    (typeII_determinant_bound_exponential r e τ 1 HT B C hr (by decide) hHT hB hC).1
  refine ⟨G^(Module.finrank ℚ K*(r*(τ+1)+Z+1)), one_le_pow₀ hG, ?_⟩
  intro s
  obtain ⟨w⟩ := hJoint s
  have h := typeII_same_matrix_exponential_denominator T w.Q U w.P A f w.b (w.δ:K)
    (2*r*((r*(τ+1)+Z+1)*(s+1))-1) ((r*(τ+1)+Z+1)*(s+1)) τ s Z
    ((r*(τ+1)+Z+1)*(s+1)) hr rfl rfl rfl hT0 hT hU w.p_degree hclear hf
    w.contact w.«prefix» e hTe w.q_degree HT B C hHT hB hC hTH w.q_house w.prefix_house
    w.coefficient_index w.rank_coefficient
  exact ⟨_, h.1, h.2.1, h.2.2⟩

end StrictEUnit
end
