import EulerCompositeConnectionArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Exact composition, not multiplication of the extracted matrix entries. -/
theorem powerSeriesEulerPolynomialConnection_mul {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (P Q : Polynomial K) (i j : Fin r) :
    powerSeriesEulerPolynomialConnection C (P*Q) i j=
      (Polynomial.aeval (powerSeriesEulerRowConnection C) P
        (fun l => powerSeriesEulerPolynomialConnection C Q i l)) j := by
  simp only [powerSeriesEulerPolynomialConnection,map_mul,Module.End.mul_apply]

theorem fallingCompositeSymbol_const (rho : K) (m q : ℕ) :
    fallingCompositeSymbol (fun _ : Unit => rho) (fun _ : Fin q => ()) (fun _ => m)=
      ((normalizedFallingSymbol (K:=K) m).comp (Polynomial.X-Polynomial.C rho))^q := by
  simp only [fallingCompositeSymbol,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem powerSeriesEulerPolynomialConnection_falling_pow {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K) (m q : ℕ) (i j : Fin r) :
    powerSeriesEulerPolynomialConnection C
      (((normalizedFallingSymbol (K:=K) m).comp (Polynomial.X-Polynomial.C rho))^q) i j=
      (((Polynomial.aeval (powerSeriesEulerRowConnection C-
        rho • (1 : Module.End K (Fin r → PowerSeries K)))
          (normalizedFallingSymbol (K:=K) m))^q)
            (fun l => (1 : Matrix (Fin r) (Fin r) (PowerSeries K)) i l)) j := by
  unfold powerSeriesEulerPolynomialConnection
  rw [map_pow,Polynomial.aeval_comp,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
    Module.algebraMap_end_eq_smul_id]
  rfl

/-- The scalar on the top logarithmic degree is an explicit product. Its
nonvanishing is NOT automatic when different exponent classes resonate. -/
theorem fallingCompositeSymbol_diagonal {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (target : K) (n : ℕ) :
    (fallingCompositeSymbol rho u ms).eval (target+(n : K))=
      ∏ i : Fin q,Ring.choose ((target-rho (u i))+(n : K)) (ms i) := by
  simp only [fallingCompositeSymbol,Polynomial.eval_prod,Polynomial.eval_comp,
    Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,normalizedFallingSymbol_eval]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

/-- If one factor kills this bounded logarithmic block, any additional
polynomial factors preserve that exact vanishing. -/
theorem frobenius_falling_log_filter_product_low_index (m n q : ℕ) (hn : n<m)
    (Q f : Polynomial K) (hf : f.natDegree≤q) :
    shiftedPolynomialDifferentialOperator (n : K)
      (Q*(normalizedFallingSymbol (K:=K) m)^(q+1)) f=0 := by
  simp only [shiftedPolynomialDifferentialOperator,map_mul,Module.End.mul_apply]
  change (Polynomial.aeval (shiftedPolynomialDerivative (n : K)) Q)
    (shiftedPolynomialDifferentialOperator (n : K)
      ((normalizedFallingSymbol (K:=K) m)^(q+1)) f)=0
  rw [frobenius_falling_log_filter_low_index m n q hn f hf,map_zero]

/-- Algebraic normalization at an arbitrary composite diagonal. This theorem
states its exact nonzero pivot, without assuming an arithmetic bound for its inverse. -/
theorem fallingCompositeFilter_diagonal_bijective {ι : Type*} (rho : ι → K) {q : ℕ}
    (u : Fin q → ι) (ms : Fin q → ℕ) (target : K) (n : ℕ)
    (hne : (∏ i : Fin q,Ring.choose ((target-rho (u i))+(n : K)) (ms i))≠0) :
    Function.Bijective (shiftedPolynomialDifferentialOperator (target+(n : K))
      (fallingCompositeSymbol rho u ms)) := by
  have he : ((fallingCompositeSymbol rho u ms).comp
      (Polynomial.X+Polynomial.C (target+(n : K)))).coeff 0≠0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_C,zero_add,fallingCompositeSymbol_diagonal]
    exact hne
  have hP : fallingCompositeSymbol rho u ms≠0 := by
    intro hz
    have hv := fallingCompositeSymbol_diagonal rho u ms target n
    rw [hz,Polynomial.eval_zero] at hv
    exact hne hv.symm
  refine ⟨?_,shiftedPolynomialDifferentialOperator_surjective _ _ hP⟩
  rw [shiftedPolynomialDifferentialOperator_eq]
  exact polynomialDifferentialOperator_injective _ he

end StrictEUnit
end
