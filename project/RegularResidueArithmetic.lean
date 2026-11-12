import RegularResidueFallingRows
import CompanionCommonDenominatorLocalBounds
import OrdinaryPointConnectionDenominators

noncomputable section
open scoped BigOperators Matrix NumberField
namespace StrictEUnit

/-- SAME integral clearing supplies exponentially bounded COMMON PREFIX
integer denominators for the actual residue binomial row. The norm factor
comes from the ORIGINAL integral trailing coefficient, without rescaling T. -/
theorem same_integral_clearing_regular_residue_denominators
    {K : Type*} [Field K] [NumberField K]
    (n : ℕ) (c : Fin (n+1) → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K) ≠ 0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K))=
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
          minimalDerivativeCompanion (n+1) c i j)
    (E : ℝ) (hE : 1 ≤ E)
    (hden : ∀ s : ℕ,∃ δ : ℕ,0<δ ∧ (δ:ℝ) ≤ E^(s+1) ∧
      ∀ m,m≤s → ∀ i j : Fin (n+1),∀ l : ℕ,
        IsIntegral ℤ ((δ:K)*(dividedPolynomialConnectionSequence
          (T.map (algebraMap (𝓞 K) K))
          (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) m i j).coeff l))
    (ht : 0<(T.map (algebraMap (𝓞 K) K)).natTrailingDegree) :
    let t := T.map (algebraMap (𝓞 K) K)
    let U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K) :=
      fun i j => (UI i j).map (algebraMap (𝓞 K) K)
    let τ := t.coeff t.natTrailingDegree
    let β := polynomialCompanionFace n 1 1 t U
    let v := T.coeff t.natTrailingDegree
    let q := Int.natAbs (Algebra.norm ℤ v)
    0<q ∧ 1 ≤ (q:ℝ)*E ∧ ∀ s : ℕ,∃ d : ℕ,
      0<d ∧ (d:ℝ) ≤ ((q:ℝ)*E)^(s+1) ∧
      ∀ m,m≤s → ∀ j : Fin (n+1),
        IsIntegral ℤ ((d:K)*regularResidueBinomialRow n τ β m j) := by
  classical
  intro t U τ β v q
  have hV := companion_common_denominators_local_bounds n c t U hT hclear E hE hden
  have hτ : τ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hT
  have hvmap : (v:K)=τ := by
    change algebraMap (𝓞 K) K (T.coeff t.natTrailingDegree)=
      (T.map (algebraMap (𝓞 K) K)).coeff t.natTrailingDegree
    rw [Polynomial.coeff_map]
  have hv : v ≠ 0 := by
    intro hz
    apply hτ
    rw [← hvmap,hz]
    rfl
  have hq : 0<q := (ringOfIntegers_natAbs_norm_certificate v hv).1
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hq)
  have hqE : 1 ≤ (q:ℝ)*E := by
    simpa only [one_mul] using mul_le_mul hq1 hE zero_le_one (Nat.cast_nonneg q)
  refine ⟨hq,hqE,?_⟩
  intro s
  obtain ⟨δ,hδ,hδbound,hδint⟩ := hden s
  refine ⟨δ*q^s,Nat.mul_pos hδ (pow_pos hq s),
    ordinaryJet_cutoff_norm_bound q δ s hq E hE hδbound,?_⟩
  intro m hm j
  let a := polynomialConnectionFaceRow n 1 1 t U m j
  have hint : IsIntegral ℤ ((δ:K)*a/(m.factorial:K)) :=
    polynomialConnectionSequence_expanded_integral t U m δ 1 Nat.one_pos 0 j
      (irregularPolynomialWeight 1 t.natTrailingDegree 1 m j.val) (hδint m hm 0 j)
  have hx := ordinaryJet_norm_power_clearing v hv δ s m hm
    (a/(m.factorial:K)) (by simpa only [div_eq_mul_inv,mul_assoc] using hint)
  have heq : ((δ*q^s:ℕ):K)*regularResidueBinomialRow n τ β m j=
      ((δ*q^s:ℕ):K)*(a/(m.factorial:K))/(v:K)^m := by
    rw [regularResidueBinomialRow_eq_normalized_face n c t U hT hclear ht hV m j,hvmap]
    change ((δ*q^s:ℕ):K)*(a/((m.factorial:K)*τ^m))=
      ((δ*q^s:ℕ):K)*(a/(m.factorial:K))/τ^m
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [heq]
  exact hx

/-- The ordinary-origin branch is retained explicitly, rather than made
singular by a change of clearing polynomial. -/
theorem polynomial_zero_trailing_degree_ordinary
    {K : Type*} [Field K] (t : Polynomial K) (ht : t ≠ 0)
    (hord : t.natTrailingDegree=0) : t.coeff 0 ≠ 0 := by
  simpa only [hord] using Polynomial.coeff_natTrailingDegree_ne_zero.mpr ht

end StrictEUnit
end
