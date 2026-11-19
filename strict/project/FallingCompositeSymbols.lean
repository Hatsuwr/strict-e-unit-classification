import FallingNewtonExpansion

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem binomial_nat_translate_cleared (x D : K) (N : ℕ)
    (h : ∀ m,m≤N → IsIntegral ℤ (D*Ring.choose x m))
    (k m : ℕ) (hm : m≤N) :
    IsIntegral ℤ (D*Ring.choose (x+(k : K)) m) := by
  rw [Ring.add_choose_eq _ (Commute.all _ _),Finset.mul_sum]
  apply IsIntegral.sum
  rintro ⟨a,b⟩ hab
  have hab' := Finset.mem_antidiagonal.mp hab
  rw [Ring.choose_natCast,← mul_assoc]
  exact (h a (by omega)).mul (ordinaryJet_natCast_integral (k.choose b))

/-- A literal product of independently shifted falling symbols. q is the
fixed number of factors, not the growing coefficient-prefix index. -/
def fallingCompositeSymbol {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) : Polynomial K :=
  ∏ i : Fin q,(normalizedFallingSymbol (K:=K) (ms i)).comp
    (Polynomial.X-Polynomial.C (rho (u i)))

theorem fallingCompositeSymbol_natDegree_le {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (N : ℕ) (hm : ∀ i,ms i≤N) :
    (fallingCompositeSymbol rho u ms).natDegree≤q*N := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i : Fin q,((normalizedFallingSymbol (K:=K) (ms i)).comp
        (Polynomial.X-Polynomial.C (rho (u i)))).natDegree ≤ ∑ _i : Fin q,N := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_comp_le).trans (by
        rw [Polynomial.natDegree_X_sub_C,mul_one]
        exact (normalizedFallingSymbol_natDegree_le (ms i)).trans (hm i))
    _ = q*N := by simp

/-- Clearing each shifted binomial prefix once per factor clears ALL natural
values of the product. The number of sample values causes no extra power. -/
theorem fallingCompositeSymbol_eval_integral {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (N : ℕ) (hm : ∀ i,ms i≤N)
    (D : K) (hD : ∀ m,m≤N → ∀ v,IsIntegral ℤ (D*Ring.choose (-rho v) m))
    (k : ℕ) : IsIntegral ℤ (D^q*(fallingCompositeSymbol rho u ms).eval (k : K)) := by
  have h (i : Fin q) : IsIntegral ℤ
      (D*((normalizedFallingSymbol (K:=K) (ms i)).comp
        (Polynomial.X-Polynomial.C (rho (u i)))).eval (k : K)) := by
    simp only [Polynomial.eval_comp,Polynomial.eval_sub,Polynomial.eval_X,
      Polynomial.eval_C,normalizedFallingSymbol_eval]
    rw [sub_eq_neg_add]
    exact binomial_nat_translate_cleared (-rho (u i)) D N (fun m hm => hD m hm (u i)) k (ms i) (hm i)
  convert IsIntegral.prod (s:=Finset.univ) _ (fun i _ => h i) using 1
  simp only [fallingCompositeSymbol,Polynomial.eval_prod,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The exact Newton expansion of a composite filter has denominator D^q,
not (q*N)! and not a product of the denominators at every sample point. -/
theorem fallingCompositeSymbol_newton_integral {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (N : ℕ) (hm : ∀ i,ms i≤N)
    (D : K) (hD : ∀ m,m≤N → ∀ v,IsIntegral ℤ (D*Ring.choose (-rho v) m)) :
    fallingNewtonSum (fallingCompositeSymbol rho u ms) (q*N)=fallingCompositeSymbol rho u ms ∧
    ∀ k,k≤q*N → IsIntegral ℤ (D^q*fallingNewtonCoefficient (fallingCompositeSymbol rho u ms) k) := by
  refine ⟨fallingNewtonSum_eq _ _ (fallingCompositeSymbol_natDegree_le rho u ms N hm),?_⟩
  exact fallingNewtonCoefficient_integral _ _ _
    (fun k _ => fallingCompositeSymbol_eval_integral rho u ms N hm D hD k)

end StrictEUnit
end
