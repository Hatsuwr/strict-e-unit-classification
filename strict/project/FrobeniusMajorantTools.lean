import FrobeniusDifferentialRatioBound

noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem shiftedPolynomialDifferentialOperator_injective_of_eval_ne
    (c : ℂ) (P : Polynomial ℂ) (h : P.eval c ≠ 0) :
    Function.Injective (shiftedPolynomialDifferentialOperator c P) := by
  rw [shiftedPolynomialDifferentialOperator_eq]
  apply polynomialDifferentialOperator_injective
  simpa only [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_comp,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,zero_add] using h

theorem shiftedPolynomialDifferentialRightInverse_neg_of_eval_ne
    (c : ℂ) (P f : Polynomial ℂ) (h : P.eval c ≠ 0) :
    shiftedPolynomialDifferentialRightInverse c P (-f) =
      -shiftedPolynomialDifferentialRightInverse c P f := by
  have hP : P ≠ 0 := by intro hz; simpa [hz] using h
  apply shiftedPolynomialDifferentialOperator_injective_of_eval_ne c P h
  rw [map_neg,shiftedPolynomialDifferentialRightInverse_apply _ _ _ hP,
    shiftedPolynomialDifferentialRightInverse_apply _ _ _ hP]

theorem shiftedPolynomialDifferentialRightInverse_sum_of_eval_ne {ι : Type*}
    (c : ℂ) (P : Polynomial ℂ) (s : Finset ι) (f : ι → Polynomial ℂ)
    (h : P.eval c ≠ 0) :
    shiftedPolynomialDifferentialRightInverse c P (∑ i ∈ s,f i) =
      ∑ i ∈ s,shiftedPolynomialDifferentialRightInverse c P (f i) := by
  have hP : P ≠ 0 := by intro hz; simpa [hz] using h
  apply shiftedPolynomialDifferentialOperator_injective_of_eval_ne c P h
  rw [map_sum,shiftedPolynomialDifferentialRightInverse_apply _ _ _ hP]
  exact Finset.sum_congr rfl (fun i hi => (shiftedPolynomialDifferentialRightInverse_apply c P (f i) hP).symm)

theorem shiftedPolynomialDifferentialRightInverse_zero_of_eval_ne
    (c : ℂ) (P : Polynomial ℂ) (h : P.eval c ≠ 0) :
    shiftedPolynomialDifferentialRightInverse c P 0 = 0 := by
  simpa using shiftedPolynomialDifferentialRightInverse_sum_of_eval_ne c P
    (∅ : Finset Unit) (fun _ => 0) h

/-- An eventual prefix-sum majorant absorbs every finite initial segment.
The geometric constant is constructed from that segment and the recurrence. -/
theorem eventually_prefix_majorant_geometric (x : ℕ → ℝ) (hx : ∀ n,0≤x n)
    (N : ℕ) (C : ℝ) (hC : 0≤C)
    (hstep : ∀ n,N≤n → x n ≤ C*∑ s : Fin n,x s.val) :
    ∃ M : ℝ,1≤M ∧ ∀ n,x n ≤ M^(n+1) := by
  let A : ℝ := 1+∑ s : Fin (N+1),x s.val
  let R : ℝ := C+1
  have hA : 1≤A := by
    have h : 0 ≤ ∑ s : Fin (N+1),x s.val := Finset.sum_nonneg (fun s hs => hx s.val)
    dsimp only [A]; linarith
  have hR : 1≤R := by dsimp only [R]; linarith
  have hb : ∀ n,x n ≤ A*R^n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : N≤n
      · have hs : (∑ s : Fin n,x s.val) ≤ A*∑ s : Fin n,R^s.val := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum (fun s hs => ih s.val s.isLt)
        have hg : C*(∑ s : Fin n,R^s.val) = R^n-1 := by
          rw [Fin.sum_univ_eq_sum_range]
          have h := mul_geom_sum R n
          have he : R-1=C := by dsimp [R]; ring
          rwa [he] at h
        calc
          x n ≤ C*∑ s : Fin n,x s.val := hstep n hn
          _ ≤ C*(A*∑ s : Fin n,R^s.val) := mul_le_mul_of_nonneg_left hs hC
          _ = A*(R^n-1) := by rw [mul_left_comm C A,hg]
          _ ≤ A*R^n := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      · have hi : n<N+1 := by omega
        have hsingle : x n ≤ ∑ s : Fin (N+1),x s.val :=
          Finset.single_le_sum (fun (s : Fin (N+1)) hs => hx s.val) (Finset.mem_univ ⟨n,hi⟩)
        have ha : x n ≤ A := by dsimp [A]; linarith
        exact ha.trans (le_mul_of_one_le_right (by linarith : 0≤A) (one_le_pow₀ hR))
  refine ⟨max A R,hA.trans (le_max_left _ _),?_⟩
  intro n
  calc
    _ ≤ A*R^n := hb n
    _ ≤ (max A R)*(max A R)^n := mul_le_mul (le_max_left _ _)
      (pow_le_pow_left₀ (by linarith) (le_max_right _ _) n) (pow_nonneg (by linarith) _) (by linarith [le_max_left A R])
    _ = _ := by rw [pow_succ]; ring

end StrictEUnit
end
