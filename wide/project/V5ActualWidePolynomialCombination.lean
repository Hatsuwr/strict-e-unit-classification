import V5BroadActualProduct
import StrictEPolynomialCombination

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- Arbitrary-epsilon arithmetic survives addition, with product denominators. -/
theorem v5_broad_algebraicArithmetic_add (a b : ℕ → AlgebraicComplex)
    (ha : V5BroadAlgebraicArithmetic a) (hb : V5BroadAlgebraicArithmetic b) :
    V5BroadAlgebraicArithmetic (fun n => a n + b n) := by
  intro ε hε
  obtain ⟨A,hA,da,hda,hdab,haa,hai⟩ := ha (ε/2) (by positivity)
  obtain ⟨B,hB,db,hdb,hdbb,hbb,hbi⟩ := hb (ε/2) (by positivity)
  have hAB : 1 ≤ A*B := one_le_mul_of_one_le_of_one_le hA hB
  have hfactor (n : ℕ) :
      (A^(n+1)*(n.factorial:ℝ)^(ε/2))*(B^(n+1)*(n.factorial:ℝ)^(ε/2)) =
      (A*B)^(n+1)*(n.factorial:ℝ)^ε := by
    have hr : (n.factorial:ℝ)^(ε/2) * (n.factorial:ℝ)^(ε/2) = (n.factorial:ℝ)^ε := by
      rw [← Real.rpow_add (by positivity), show ε/2+ε/2=ε by ring]
    rw [mul_pow]
    calc
      _ = (A^(n+1)*B^(n+1))*((n.factorial:ℝ)^(ε/2)*(n.factorial:ℝ)^(ε/2)) := by ring
      _ = _ := by rw [hr]
  have hbase (C : ℝ) (hC : 1 ≤ C) (n : ℕ) :
      1 ≤ C^(n+1)*(n.factorial:ℝ)^(ε/2) :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hC)
      (Real.one_le_rpow (by exact_mod_cast Nat.factorial_pos n) (by positivity))
  have hscale (n : ℕ) :
      2*((A*B)^(n+1)*(n.factorial:ℝ)^ε) ≤ (2*(A*B))^(n+1)*(n.factorial:ℝ)^ε := by
    have ht : (2:ℝ) ≤ 2^(n+1) := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (show 1 ≤ n+1 by omega)
    calc
      _ ≤ 2^(n+1)*((A*B)^(n+1)*(n.factorial:ℝ)^ε) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
      _ = _ := by rw [mul_pow]; ring
  refine ⟨2*(A*B),by nlinarith,fun L => da L*db L,
    fun L => Nat.mul_pos (hda L) (hdb L),?_,?_,?_⟩
  · intro L
    push_cast
    calc
      (da L:ℝ)*(db L:ℝ) ≤ _ := mul_le_mul (hdab L) (hdbb L) (by positivity) (by positivity)
      _ = (A*B)^(L+1)*(L.factorial:ℝ)^ε := hfactor L
      _ ≤ 2*((A*B)^(L+1)*(L.factorial:ℝ)^ε) := by nlinarith [show 0 ≤ (A*B)^(L+1)*(L.factorial:ℝ)^ε by positivity]
      _ ≤ _ := hscale L
  · intro τ n
    rw [map_add]
    have ha' := le_mul_of_one_le_right (show 0 ≤ A^(n+1)*(n.factorial:ℝ)^(ε/2) by positivity) (hbase B hB n)
    have hb' := le_mul_of_one_le_left (show 0 ≤ B^(n+1)*(n.factorial:ℝ)^(ε/2) by positivity) (hbase A hA n)
    rw [hfactor] at ha' hb'
    calc
      ‖τ (a n) + τ (b n)‖ ≤ ‖τ (a n)‖ + ‖τ (b n)‖ := norm_add_le _ _
      _ ≤ 2*((A*B)^(n+1)*(n.factorial:ℝ)^ε) := by linarith [haa τ n, hbb τ n]
      _ ≤ _ := hscale n
  · intro L n hn
    have hdaI : IsIntegral ℤ (da L : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (da L : ℤ)))
    have hdbI : IsIntegral ℤ (db L : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (db L : ℤ)))
    have ha' := hdbI.mul (hai L n hn)
    have hb' := hdaI.mul (hbi L n hn)
    convert ha'.add hb' using 1
    push_cast
    ring

/-- Full actual wide closure under addition, including a nonzero polynomial ODE. -/
theorem v5_broad_actual_add {f g : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hg : V5IsBroadEFunction g) :
    V5IsBroadEFunction (fun z => f z + g z) := by
  obtain ⟨a,hdf,hsf,hof,ha⟩ := hf
  obtain ⟨b,hdg,hsg,hog,hb⟩ := hg
  refine ⟨fun n => a n + b n, hdf.add hdg, ?_, ?_,
    v5_broad_algebraicArithmetic_add a b ha hb⟩
  · intro z
    exact strictE_egf_hasSum_add (hsf z) (hsg z)
  · exact (stage14_algebraicPolynomialODE_iff_subfield _).mpr
      (stage14_actualSubfieldODE_add (algebraicClosure ℚ ℂ).toSubfield
        (v5FactorialEntire f hdf a hsf) (v5FactorialEntire g hdg b hsg) hof hog)

theorem v5_broad_actual_finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, V5IsBroadEFunction (f i)) :
    V5IsBroadEFunction (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using v5_strict_is_broad (algebraic_constant_isStrictEFunction (0 : AlgebraicComplex))
  | @insert i s hi ih =>
    have hs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using
      v5_broad_actual_add (hf i (Finset.mem_insert_self i s)) hs

theorem v5_broad_actual_polynomialEvaluation (p : Polynomial AlgebraicComplex) :
    V5IsBroadEFunction (fun z => p.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z) :=
  v5_strict_is_broad (strictEFunction_polynomialEvaluation p)

/-- The actual cyclic scalar candidate is wide, including for an empty index type. -/
theorem v5_broad_actual_polynomialCombination {ι : Type*} [Fintype ι]
    (p : ι → Polynomial AlgebraicComplex) (f : ι → ℂ → ℂ)
    (hf : ∀ i, V5IsBroadEFunction (f i)) :
    V5IsBroadEFunction (fun z => ∑ i,
      (p i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * f i z) := by
  apply v5_broad_actual_finsetSum
  intro i hi
  exact v5_broad_actual_mul (v5_broad_actual_polynomialEvaluation (p i)) (hf i)

#print axioms v5_broad_algebraicArithmetic_add
#print axioms v5_broad_actual_add
#print axioms v5_broad_actual_finsetSum
#print axioms v5_broad_actual_polynomialCombination
end StrictEUnit
