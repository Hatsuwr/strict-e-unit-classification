import DiagonalBinomialSharedInverse
import FallingLogNormalizationBounds

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- A finite family admits one common diagonal inverse denominator. No
noncollision hypothesis is imposed: the zero terms are explicitly excluded. -/
theorem finite_diagonalBinomial_shared_inverse {ι : Type*} [Fintype ι]
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧
      ∀ i n,n≤N → Ring.choose (rho i+(n : K)) n≠0 →
        IsIntegral ℤ ((e : K)*(Ring.choose (rho i+(n : K)) n)⁻¹) := by
  classical
  have h (i : ι) : DiagonalBinomialInversePrefixDenominators (rho i) := by
    apply diagonalBinomial_shared_inverse
    obtain ⟨B,hB,hden⟩ := hrho
    exact ⟨B,hB,fun N => by
      obtain ⟨D,hD,hDb,hDi⟩ := hden N
      exact ⟨D,hD,hDb,fun m hm => hDi m hm i⟩⟩
  choose C hC hpre using h
  refine ⟨∏ i,C i,?_,?_⟩
  · simpa using (Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _ : ι => (1 : ℝ)) (g:=C) (fun _ _ => zero_le_one) (fun i _ => hC i))
  · intro N
    choose e he heb hei using (fun i => hpre i N)
    refine ⟨∏ i,e i,Finset.prod_pos (fun i _ => he i),?_,?_⟩
    · rw [Nat.cast_prod]
      exact (Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => heb i)).trans_eq
        (Finset.prod_pow Finset.univ (N+1) C)
    · intro i n hn hne
      obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem e (Finset.mem_univ i)
      rw [hb,Nat.cast_mul]
      convert (hei i n hn hne).mul (ordinaryJet_natCast_integral (K:=K) b) using 1 <;> ring

/-- Fixed-length products retain a common exponential bound, even when
factors are repeated. Every order is the SAME n as the natural target shift. -/
theorem diagonalComposite_shared_inverse {ι : Type*} [Fintype ι]
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧
      ∀ (u : Fin q → ι) n,n≤N → binomialCompositeValue rho u (fun _ => n) n≠0 →
        IsIntegral ℤ ((e : K)*(binomialCompositeValue rho u (fun _ => n) n)⁻¹) := by
  obtain ⟨C,hC,hden⟩ := finite_diagonalBinomial_shared_inverse rho hrho
  refine ⟨C^q,one_le_pow₀ hC,?_⟩
  intro N
  obtain ⟨e,he,heb,hei⟩ := hden N
  refine ⟨e^q,pow_pos he _,?_,?_⟩
  · rw [Nat.cast_pow,pow_right_comm]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) heb q
  · intro u n hn hp
    have hf (i : Fin q) : Ring.choose (rho (u i)+(n : K)) n≠0 :=
      (Finset.prod_ne_zero_iff.mp hp) i (Finset.mem_univ _)
    convert IsIntegral.prod (s:=Finset.univ) _ (fun i _ => hei (u i) n hn (hf i)) using 1
    simp only [binomialCompositeValue,Nat.cast_pow,Finset.prod_mul_distrib,
      Finset.prod_const,Finset.card_univ,Fintype.card_fin,Finset.prod_inv_distrib]

/-- This applies to actual falling-filter pivots for every pair of classes;
no premise says that all exponents lie in a single integer-shift class. -/
theorem fallingComposite_diagonal_shared_inverse {ι : Type*} [Fintype ι]
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) (q : ℕ) :
    ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧
      ∀ (u : Fin q → ι) v n,n≤N →
        (fallingCompositeSymbol rho u (fun _ => n)).eval (rho v+(n : K))≠0 →
        IsIntegral ℤ ((e : K)*
          ((fallingCompositeSymbol rho u (fun _ => n)).eval (rho v+(n : K)))⁻¹) := by
  obtain ⟨C,hC,hden⟩ := diagonalComposite_shared_inverse
    (fun ij : ι × ι => rho ij.1-rho ij.2) (jointBinomialPrefixDenominators_sub rho hrho) q
  refine ⟨C,hC,?_⟩
  intro N
  obtain ⟨e,he,heb,hei⟩ := hden N
  refine ⟨e,he,heb,?_⟩
  intro u v n hn hp
  simpa only [binomialCompositeValue,fallingCompositeSymbol_diagonal] using
    hei (fun i => (v,u i)) n hn (by simpa only [binomialCompositeValue,fallingCompositeSymbol_diagonal] using hp)

end StrictEUnit
end
