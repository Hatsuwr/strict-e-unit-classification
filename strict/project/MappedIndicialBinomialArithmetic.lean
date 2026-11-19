import RegularResidueFieldMap
import RegularIndicialBinomialArithmetic

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- A finite algebraic vector has one derived positive integer clearing. -/
theorem exists_positive_nat_integral_algebraic_vector
    {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℤ K] {r : ℕ} (v : Fin r → K) :
    ∃ b : ℕ,0<b ∧ ∀ j,IsIntegral ℤ ((b:K)*v j) := by
  classical
  obtain ⟨z,hz,hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image v)
  have hi (j : Fin r) : IsIntegral ℤ ((z:K)*v j) := by
    have h := hint (v j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩)
    simpa only [Algebra.smul_def] using h
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
theorem algebraic_regularResidueIndicial_binomial_denominators
    {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℤ K]
    (n : ℕ) (τ : K) (β : Fin (n+1) → K) (ξ : K)
    (hξ : (regularResidueIndicial n τ β).eval ξ=0)
    (D : ℝ) (hD : 1≤D)
    (hden : ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤D^(s+1) ∧
      ∀ m,m≤s → ∀ j : Fin (n+1),IsIntegral ℤ ((d:K)*regularResidueBinomialRow n τ β m j)) :
    ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
      ∀ m,m≤s → IsIntegral ℤ ((d:K)*((descPochhammer K m).eval ξ/(m.factorial:K))) := by
  classical
  let v : Fin (n+1) → K := fun j => (descPochhammer K j.val).eval ξ
  obtain ⟨b,hb,hbint⟩ := exists_positive_nat_integral_algebraic_vector v
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


/-- The SAME source clearing derives binomial arithmetic for roots in ANY
algebraic field extension, with the original witnesses mapped literally. -/
theorem same_clearing_mapped_indicial_binomial_denominators
    {K L : Type*} [Field K] [NumberField K] [Field L] [CharZero L]
    [Algebra.IsAlgebraic ℤ L]
    (φ : K →+* L) (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
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
    (ξ : L)
    (hξ : (regularResidueIndicial n
      (φ ((T.map (algebraMap (𝓞 K) K)).coeff (T.map (algebraMap (𝓞 K) K)).natTrailingDegree))
      (fun j => φ (polynomialCompanionFace n 1 1 (T.map (algebraMap (𝓞 K) K))
        (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) j))).eval ξ=0) :
    ∃ C : ℝ,1≤C ∧ ∀ s : ℕ,∃ d : ℕ,0<d ∧ (d:ℝ)≤C^(s+1) ∧
      ∀ m,m≤s → IsIntegral ℤ ((d:L)*((descPochhammer L m).eval ξ/(m.factorial:L))) := by
  obtain ⟨hq,hqE,hrows⟩ :=
    same_integral_clearing_regular_residue_denominators n c T UI hT hclear E hE hden ht
  apply algebraic_regularResidueIndicial_binomial_denominators n _ _ ξ hξ _ hqE
  intro s
  obtain ⟨d,hd,hdbound,hdint⟩ := hrows s
  refine ⟨d,hd,hdbound,?_⟩
  intro m hm j
  have h := (hdint m hm j).map φ.toIntAlgHom
  simpa only [RingHom.toIntAlgHom_apply,map_mul,map_natCast,regularResidueBinomialRow_map] using h

end StrictEUnit
end
