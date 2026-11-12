import DiagonalCompositeLogNormalization
import AllClassPrefixConnectionArithmetic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- Repeated filters are literally one repeated-index composite; this is a
polynomial identity, not an identification of scalar and matrix products. -/
theorem fallingCompositeSymbol_pow_reindex {ι : Type*} (rho : ι → K)
    {q : ℕ} (u : Fin q → ι) (n p : ℕ) :
    (fallingCompositeSymbol rho u (fun _ => n))^p =
      fallingCompositeSymbol rho (fun i : Fin (q*p) => u (finProdFinEquiv.symm i).1)
        (fun _ => n) := by
  unfold fallingCompositeSymbol
  have h := Equiv.prod_comp (finProdFinEquiv : Fin q × Fin p ≃ Fin (q*p))
    (fun i : Fin (q*p) => (normalizedFallingSymbol (K:=K) n).comp
      (Polynomial.X-Polynomial.C (rho (u (finProdFinEquiv.symm i).1))))
  rw [← h]
  simp only [Equiv.symm_apply_apply,Fintype.prod_prod_type,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,Finset.prod_pow]

/-- The actual all-class filter has a common exponential bounded-log
normalizer at all NONZERO boundary pivots. Its scalar pivot depends only on
exponent differences, not on the chosen integer lower Laurent bound. -/
theorem allClassPrefixFilter_shared_log_normalization {q : ℕ} (rho : Fin q → K)
    (hrho : JointBinomialPrefixDenominators rho) (L : ℤ) (d : ℕ) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤B^(N+1) ∧
      ∀ v n,n≤N → (allClassPrefixFilter rho L n d).eval (rho v+(L : K)+(n : K))≠0 →
        ∀ (Z : K) (f : Polynomial K),f.natDegree≤d →
          (∀ j,IsIntegral ℤ (Z*(shiftedPolynomialDifferentialOperator (rho v+(L : K)+(n : K))
            (allClassPrefixFilter rho L n d) f).coeff j)) →
          ∀ j,IsIntegral ℤ ((e : K)*Z*f.coeff j) := by
  obtain ⟨B,hB,hden⟩ := fallingComposite_diagonal_shared_log_normalization
    (fun i => rho i+(L : K)) (jointBinomialPrefixDenominators_integer_shift rho hrho L)
    (q*(d+1)) d
  refine ⟨B,hB,?_⟩
  intro N
  obtain ⟨e,he,heb,hei⟩ := hden N
  refine ⟨e,he,heb,?_⟩
  intro v n hn hp Z f hf hforced j
  have hid : allClassPrefixFilter rho L n d =
      fallingCompositeSymbol (fun i => rho i+(L : K))
        (fun i : Fin (q*(d+1)) => (finProdFinEquiv.symm i).1) (fun _ => n) := by
    exact fallingCompositeSymbol_pow_reindex _ id n (d+1)
  rw [hid] at hp hforced
  exact hei _ v n hn hp Z f hf hforced j

end StrictEUnit
end
