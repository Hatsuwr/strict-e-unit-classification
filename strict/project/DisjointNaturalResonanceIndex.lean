import DisjointNaturalExponentClasses
import FourierNaturalResonanceBasis

noncomputable section
open scoped Classical
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

/-- The actual root-seed map of all disjoint lower classes is bijective.
This retains root multiplicities, not merely the set of distinct exponents. -/
theorem disjointNaturalResonanceSeed_bijective
    (P : Polynomial K) (hP : P ≠ 0) (e : frobeniusRootSeedIndex P ≃ Fin r)
    (rho : Fin r → K) (hrho : ∀ j, rho j = frobeniusRootSeedExponent P (e.symm j))
    (xi : ExponentClass rho → K) (s : Fin r → ℕ)
    (hs : ∀ j, rho j = xi (exponentClassMap rho j) + (s j : K))
    (hsep : ∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) :
    Function.Bijective (fun i : Σ c, polynomialLogResonanceCoordinateIndex (xi c) P =>
      naturalResonanceRootSeed P (xi i.1) hP i.2) := by
  classical
  constructor
  · intro i j he
    have hx : xi i.1 + (i.2.1.1 : K) = xi j.1 + (j.2.1.1 : K) :=
      congrArg (fun a : frobeniusRootSeedIndex P => a.1.1) he
    have hc : i.1 = j.1 := by
      by_contra hn
      apply hsep i.1 j.1 hn ((j.2.1.1 : ℤ) - (i.2.1.1 : ℤ))
      push_cast
      linear_combination hx
    cases i with | mk c i =>
      cases j with | mk d j =>
        dsimp only at hc
        subst d
        have hn : i.1.1 = j.1.1 := by
          have hn' : (i.1.1 : K) = (j.1.1 : K) := add_left_cancel hx
          exact_mod_cast hn'
        have hnsub : i.1 = j.1 := Subtype.ext hn
        have hi : i = j := by
          apply Sigma.ext hnsub
          apply (Fin.heq_ext_iff (by congr 1)).mpr
          exact congrArg (fun a : frobeniusRootSeedIndex P => a.2.1) he
        cases hi
        rfl
  · intro a
    let j := e a
    have hj : rho j = a.1.1 := by simpa [j, frobeniusRootSeedExponent] using hrho j
    have hx : xi (exponentClassMap rho j) + (s j : K) = a.1.1 := (hs j).symm.trans hj
    have hm : s j ∈ polynomialResonanceIndices (xi (exponentClassMap rho j)) P := by
      apply (polynomialResonanceIndices_mem_iff_eval_zero _ P hP _).mpr
      rw [hx]
      exact (Polynomial.mem_roots hP).mp (Multiset.mem_toFinset.mp a.1.2)
    have hmult : polynomialResonanceMultiplicity (xi (exponentClassMap rho j)) P (s j) =
        P.rootMultiplicity a.1.1 := by
      unfold polynomialResonanceMultiplicity
      rw [hx]
    let i : polynomialLogResonanceCoordinateIndex (xi (exponentClassMap rho j)) P :=
      ⟨⟨s j, hm⟩, ⟨a.2.1, by rw [hmult]; exact a.2.2⟩⟩
    refine ⟨⟨exponentClassMap rho j, i⟩, ?_⟩
    apply Sigma.ext (Subtype.ext hx)
    apply (Fin.heq_ext_iff (by congr 1)).mpr
    rfl

/-- Global natural-resonance indexing has exactly the original scalar rank. -/
theorem exists_disjoint_natural_resonance_equiv
    (P : Polynomial K) (hP : P ≠ 0) (e : frobeniusRootSeedIndex P ≃ Fin r)
    (rho : Fin r → K) (hrho : ∀ j, rho j = frobeniusRootSeedExponent P (e.symm j)) :
    ∃ xi : ExponentClass rho → K, ∃ s : Fin r → ℕ,
      (∀ j, rho j = xi (exponentClassMap rho j) + (s j : K)) ∧
      (∀ c d, c ≠ d → ∀ z : ℤ, xi c - xi d ≠ (z : K)) ∧
      ∃ E : (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) ≃ Fin r,
        (∀ i, E i = e (naturalResonanceRootSeed P (xi i.1) hP i.2)) ∧
        Nat.card (Σ c, polynomialLogResonanceCoordinateIndex (xi c) P) = r := by
  classical
  obtain ⟨xi, s, hs, hsep⟩ := exists_disjoint_natural_exponent_classes rho
  let f := fun i : Σ c, polynomialLogResonanceCoordinateIndex (xi c) P =>
    naturalResonanceRootSeed P (xi i.1) hP i.2
  let E := (Equiv.ofBijective f
    (disjointNaturalResonanceSeed_bijective P hP e rho hrho xi s hs hsep)).trans e
  refine ⟨xi, s, hs, hsep, E, fun _ => rfl, ?_⟩
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_fin]

end StrictEUnit
end
