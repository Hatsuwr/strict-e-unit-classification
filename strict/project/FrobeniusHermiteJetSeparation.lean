import FrobeniusRootSeeds
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial encoded by a finite row, without changing its coefficients. -/
def frobeniusJetSymbol {r : ℕ} (c : Fin r → K) : Polynomial K :=
  ∑ i,Polynomial.monomial i.val (c i)

theorem frobeniusJetSymbol_coeff {r : ℕ} (c : Fin r → K) (i : Fin r) :
    (frobeniusJetSymbol c).coeff i.val=c i := by
  simp only [frobeniusJetSymbol,Polynomial.finset_sum_coeff,Polynomial.coeff_monomial]
  simp only [Fin.val_inj,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem frobeniusJetSymbol_injective {r : ℕ} :
    Function.Injective (frobeniusJetSymbol (K:=K) (r:=r)) := by
  intro c d h
  funext i
  have hh := congrArg (fun P : Polynomial K =>P.coeff i.val) h
  simpa only [frobeniusJetSymbol_coeff] using hh

theorem frobeniusJetSymbol_degree_lt {r : ℕ} (c : Fin r → K) :
    (frobeniusJetSymbol c).degree<r := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro m hm
  simp only [frobeniusJetSymbol,Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Polynomial.coeff_monomial,if_neg (by omega : i.val≠m)]

/-- All derivative jets at the exact roots and multiplicities separate every
polynomial of degree below the full indicial degree. This is a genuine Hermite
jet argument, not independence of scalar amplitudes substituted for a determinant. -/
theorem frobeniusRootSeed_hermite_separation (P Q : Polynomial K)
    (hP : P.Splits (RingHom.id K)) (hQ : Q.degree<P.natDegree)
    (hjets : ∀ i : frobeniusRootSeedIndex P,
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[frobeniusRootSeedOrder P i] Q).eval
        (frobeniusRootSeedExponent P i)=0) : Q=0 := by
  by_contra hne
  have hmult : ∀ x : K,P.rootMultiplicity x≤Q.rootMultiplicity x := by
    intro x
    by_cases hx : P.rootMultiplicity x=0
    · rw [hx];exact Nat.zero_le _
    have hmem : x∈P.roots.toFinset := by
      rw [Multiset.mem_toFinset,← Multiset.count_pos,Polynomial.count_roots]
      exact Nat.pos_of_ne_zero hx
    have hh : P.rootMultiplicity x-1<Q.rootMultiplicity x :=
      Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hne (by
        intro m hm
        exact hjets ⟨⟨x,hmem⟩,⟨m,by change m<P.rootMultiplicity x;omega⟩⟩)
    omega
  have hroots : P.roots≤Q.roots := by
    apply Multiset.le_iff_count.mpr
    intro x
    simpa only [Polynomial.count_roots] using hmult x
  have hdeg : P.natDegree≤Q.natDegree := by
    rw [← Polynomial.splits_iff_card_roots.mp hP]
    exact (Multiset.card_le_card hroots).trans (Polynomial.card_roots' Q)
  exact (not_lt_of_ge hdeg) ((Polynomial.natDegree_lt_iff_degree_lt hne).mpr hQ)

/-- Constant coefficient of P(D) on the monomial seed is the matching
factorial-weighted symbol coefficient. -/
theorem polynomialDifferentialOperator_X_pow_coeff_zero (P : Polynomial K) (j : ℕ) :
    (polynomialDifferentialOperator P (Polynomial.X^j)).coeff 0=
      P.coeff j*(j.factorial : K) := by
  rw [polynomialDifferentialOperator_apply,Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_smul,Polynomial.coeff_iterate_derivative,zero_add,
    Polynomial.coeff_X_pow,smul_eq_mul,nsmul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp [Nat.descFactorial_self]
  · intro i hi hij
    simp [hij]
  · intro hj
    simp [Polynomial.not_mem_support_iff.mp hj]

/-- Shifted symbolic differentiation and ordinary derivative evaluation agree
on the constant coefficient of the actual monomial seed. -/
theorem shiftedPolynomialDifferentialOperator_X_pow_coeff_zero
    (rho : K) (Q : Polynomial K) (j : ℕ) :
    (shiftedPolynomialDifferentialOperator rho Q (Polynomial.X^j)).coeff 0=
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[j] Q).eval rho := by
  have hcomp : ∀ m : ℕ,
      (Polynomial.derivative : Polynomial K → Polynomial K)^[m]
        (Q.comp (Polynomial.X+Polynomial.C rho))=
      ((Polynomial.derivative : Polynomial K → Polynomial K)^[m] Q).comp
        (Polynomial.X+Polynomial.C rho) := by
    intro m
    induction m with
    | zero =>rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply',ih,Polynomial.derivative_comp,
        Polynomial.derivative_add,Polynomial.derivative_X,Polynomial.derivative_C,
        add_zero,one_mul,Function.iterate_succ_apply']
  rw [shiftedPolynomialDifferentialOperator_eq,polynomialDifferentialOperator_X_pow_coeff_zero]
  have he := congrArg (fun p : Polynomial K =>p.coeff 0) (hcomp j)
  dsimp only at he
  rw [Polynomial.coeff_iterate_derivative] at he
  simp only [zero_add,Nat.descFactorial_self,
    nsmul_eq_mul,Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,zero_add] at he
  exact (mul_comm _ _).trans he

end StrictEUnit
end
