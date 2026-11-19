import RegularResidueIndicialRoots
import RegularResidueArithmetic
import IntegralRationalMatrixClearing

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- A finite number-field vector has one derived positive integer clearing. -/
theorem exists_positive_nat_integral_vector
    {K : Type*} [Field K] [NumberField K] {r : ℕ} (v : Fin r → K) :
    ∃ b : ℕ,0<b ∧ ∀ j,IsIntegral ℤ ((b:K)*v j) := by
  classical
  obtain ⟨z,hz,P,hP⟩ := exists_integer_polynomial_family_lift K (fun j => Polynomial.C (v j))
  have hi (j : Fin r) : IsIntegral ℤ ((z:K)*v j) := by
    have hc := congrArg (fun p : Polynomial K => p.coeff 0) (hP j)
    simp only [Polynomial.coeff_map,Polynomial.coeff_C_mul,Polynomial.coeff_C,
      if_pos rfl,mul_one] at hc
    have h := NumberField.RingOfIntegers.isIntegral_coe ((P j).coeff 0)
    rw [hc] at h
    exact h
  let b := z.natAbs
  have hb : 0<b := Int.natAbs_pos.mpr hz
  have he : (b:ℤ)=z ∨ (b:ℤ)= -z := by
    rw [show (b:ℤ)=|z| from Int.natCast_natAbs z]
    by_cases h : 0≤z
    · exact Or.inl (abs_of_nonneg h)
    · exact Or.inr (abs_of_neg (lt_of_not_ge h))
  refine ⟨b,hb,?_⟩
  intro j
  rcases he with he | he
  · have hc : (b:K)=(z:K) := by exact_mod_cast he
    rw [hc]
    exact hi j
  · have hc : (b:K)= -(z:K) := by exact_mod_cast he
    rw [hc]
    simpa only [neg_mul] using (hi j).neg

/-- The explicit indicial eigenvector transfers common-prefix arithmetic of
residue rows to the ACTUAL scalar binomial sequence. No rationality premise. -/
theorem regularResidueIndicial_binomial_denominators
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (τ : K) (β : Fin (n+1) → K) (ξ : K)
    (hξ : (regularResidueIndicial n τ β).eval ξ=0)
    (D : ℝ) (hD : 1≤D)
    (hden : ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤D^(s+1) ∧
      ∀ m,m≤s → ∀ j : Fin (n+1),IsIntegral ℤ ((d:K)*regularResidueBinomialRow n τ β m j)) :
    ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
      ∀ m,m≤s → IsIntegral ℤ ((d:K)*((descPochhammer K m).eval ξ/(m.factorial:K))) := by
  classical
  let v : Fin (n+1) → K := fun j => (descPochhammer K j.val).eval ξ
  obtain ⟨b,hb,hbint⟩ := exists_positive_nat_integral_vector v
  have hb1 : (1:ℝ)≤(b:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hb)
  have hb0 : (0:ℝ)≤(b:ℝ) := Nat.cast_nonneg b
  refine ⟨(b:ℝ)*D,?_,?_⟩
  · simpa only [one_mul] using mul_le_mul hb1 hD zero_le_one hb0
  · intro s
    obtain ⟨d,hd,hdbound,hdint⟩ := hden s
    refine ⟨b*d,Nat.mul_pos hb hd,?_,?_⟩
    · rw [Nat.cast_mul,mul_pow]
      exact (mul_le_mul_of_nonneg_left hdbound hb0).trans
        (mul_le_mul_of_nonneg_right (le_self_pow₀ hb1 (Nat.succ_ne_zero s))
          (pow_nonneg (le_trans zero_le_one hD) (s+1)))
    · intro m hm
      rw [← regularResidueBinomialRow_indicial_pairing n τ β ξ hξ m]
      change IsIntegral ℤ (((b*d:ℕ):K)*∑ j,regularResidueBinomialRow n τ β m j*v j)
      rw [Finset.mul_sum]
      apply IsIntegral.sum
      intro j hj
      convert (hdint m hm j).mul (hbint j) using 1
      simp only [Nat.cast_mul]
      ring

/-- Original SAME clearing and its original denominator certificate derive
scalar binomial arithmetic for every root IN that coefficient number field.
Transport to a splitting field is a separate universal field-map bridge. -/
theorem same_integral_clearing_indicial_binomial_denominators
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K))=
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
          minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1≤E)
    (hden : ∀ s : ℕ,∃ δ : ℕ,0<δ ∧ (δ:ℝ)≤E^(s+1) ∧
      ∀ m,m≤s → ∀ i j : Fin (n+1),∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) m i j).coeff l))
    (ht : 0<(T.map (algebraMap (𝓞 K) K)).natTrailingDegree)
    (ξ : K)
    (hξ : (regularResidueIndicial n
      ((T.map (algebraMap (𝓞 K) K)).coeff (T.map (algebraMap (𝓞 K) K)).natTrailingDegree)
      (polynomialCompanionFace n 1 1 (T.map (algebraMap (𝓞 K) K))
        (fun i j => (UI i j).map (algebraMap (𝓞 K) K)))).eval ξ=0) :
    ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
      ∀ m,m≤s → IsIntegral ℤ ((d:K)*((descPochhammer K m).eval ξ/(m.factorial:K))) := by
  obtain ⟨hq,hqE,hrows⟩ :=
    same_integral_clearing_regular_residue_denominators n c T UI hT hclear E hE hden ht
  exact regularResidueIndicial_binomial_denominators n _ _ ξ hξ _ hqE hrows

end StrictEUnit
end
