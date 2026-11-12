import FrobeniusMajorantTools

/-! The actual triangular Frobenius recurrence has factorial-normalized
geometric coefficient growth. Finite early resonances are absorbed by a proved
prefix majorant, not excluded by a global nonresonance hypothesis. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

theorem triangularFrobenius_factorial_geometric_bound
    (B : ℕ → Polynomial ℂ) (rho : ℂ) (u0 : Polynomial ℂ) (ν : ℕ)
    (hP : B 0 ≠ 0) (hdegree : (B 0).natDegree = ν)
    (hzero : ∀ k,ν<k → B k=0) (hdeg : ∀ k,(B k).natDegree ≤ ν-k) :
    ∃ C : ℝ,1≤C ∧ ∀ n : ℕ,
      (n.factorial : ℝ)*polynomialLogSize (u0.natDegree+ν)
        (polynomialLogFrobeniusCoefficient B rho u0 n) ≤ C^(n+1) := by
  let d := u0.natDegree+ν
  let u := polynomialLogFrobeniusCoefficient B rho u0
  have hud (n : ℕ) : (u n).natDegree ≤ d := by
    simpa only [d,hdegree] using polynomialLogFrobeniusCoefficient_uniform_degree B rho u0 n
  have hest : ∀ k : Fin (ν+1),∃ N : ℕ,∃ C : ℝ,0<C ∧
      ∀ n : ℕ,N≤n → ∀ f : Polynomial ℂ,f.natDegree≤d →
      (n.descFactorial k.val : ℝ)*polynomialLogSize d
        (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) (B 0)
          (shiftedPolynomialDifferentialOperator ((rho-(k.val : ℂ))+(n : ℂ)) (B k.val) f)) ≤
          C*polynomialLogSize d f := by
    intro k
    apply complexPolynomial_eventually_differential_factorial_ratio_bound
      (B 0) (B k.val) hP rho (rho-(k.val : ℂ)) d k.val
    · rw [hdegree]; omega
    · rw [hdegree]; exact hdeg k.val
  choose N C hC hbound using hest
  obtain ⟨N₀,C₀,hC₀,hscalar⟩ := complexPolynomial_eventually_inverse_bound (B 0) hP rho
  let L : ℕ := max 1 (max N₀ (Finset.univ.sup N))
  let M : ℝ := ∑ k : Fin (ν+1),C k
  have hM : 0≤M := Finset.sum_nonneg (fun k hk => le_of_lt (hC k))
  let x (n : ℕ) := (n.factorial : ℝ)*polynomialLogSize d (u n)
  have hx (n : ℕ) : 0≤x n := mul_nonneg (Nat.cast_nonneg _) (polynomialLogSize_nonneg d _)
  apply eventually_prefix_majorant_geometric x hx L M hM
  intro n hn
  have hn0 : n≠0 := by have := (le_max_left 1 (max N₀ (Finset.univ.sup N))).trans hn; omega
  have hnN₀ : N₀≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hne := (hscalar n hnN₀).1
  have hnN (k : Fin (ν+1)) : N k ≤ n :=
    (Finset.le_sup (f := N) (Finset.mem_univ k)).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have he : u n = -(∑ s : Fin n,
      shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) (B 0)
        (shiftedPolynomialDifferentialOperator (rho+(s.val : ℂ)) (B (n-s.val)) (u s.val))) := by
    dsimp only [u]
    rw [polynomialLogFrobeniusCoefficient_eq,if_neg hn0,
      shiftedPolynomialDifferentialRightInverse_neg_of_eval_ne _ _ _ hne,
      polynomialLogLowerSum,shiftedPolynomialDifferentialRightInverse_sum_of_eval_ne _ _ _ _ hne]
  have hterm (s : Fin n) :
      (n.factorial : ℝ)*polynomialLogSize d
        (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) (B 0)
          (shiftedPolynomialDifferentialOperator (rho+(s.val : ℂ)) (B (n-s.val)) (u s.val))) ≤ M*x s.val := by
    by_cases hk : n-s.val≤ν
    · let k : Fin (ν+1) := ⟨n-s.val,by omega⟩
      have hec : (rho-(k.val : ℂ))+(n : ℂ) = rho+(s.val : ℂ) := by
        dsimp only [k]
        rw [Nat.cast_sub (le_of_lt s.isLt)]
        ring
      have hb := hbound k n (hnN k) (u s.val) (hud s.val)
      rw [hec] at hb
      have hcM : C k ≤ M := Finset.single_le_sum (fun j hj => le_of_lt (hC j)) (Finset.mem_univ k)
      have hfac : (n.factorial : ℝ) = (s.val.factorial : ℝ)*(n.descFactorial k.val : ℝ) := by
        have h := Nat.factorial_mul_descFactorial (show n-s.val≤n by omega)
        rw [Nat.sub_sub_self (le_of_lt s.isLt)] at h
        exact_mod_cast h.symm
      rw [hfac,mul_assoc]
      calc
        _ ≤ (s.val.factorial : ℝ)*(C k*polynomialLogSize d (u s.val)) :=
          mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
        _ = C k*x s.val := by dsimp [x]; ring
        _ ≤ M*x s.val := mul_le_mul_of_nonneg_right hcM (hx s.val)
    · rw [hzero _ (Nat.lt_of_not_ge hk)]
      simp only [shiftedPolynomialDifferentialOperator,map_zero,LinearMap.zero_apply,
        shiftedPolynomialDifferentialRightInverse_zero_of_eval_ne _ _ hne,
        polynomialLogSize_zero,mul_zero]
      exact mul_nonneg hM (hx s.val)
  change (n.factorial : ℝ)*polynomialLogSize d (u n) ≤ _
  rw [he,polynomialLogSize_neg]
  calc
    _ ≤ (n.factorial : ℝ)*∑ s : Fin n,polynomialLogSize d
        (shiftedPolynomialDifferentialRightInverse (rho+(n : ℂ)) (B 0)
          (shiftedPolynomialDifferentialOperator (rho+(s.val : ℂ)) (B (n-s.val)) (u s.val))) :=
      mul_le_mul_of_nonneg_left (polynomialLogSize_sum_le d Finset.univ _) (Nat.cast_nonneg _)
    _ ≤ ∑ s : Fin n,M*x s.val := by rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun s hs => hterm s)
    _ = M*∑ s : Fin n,x s.val := (Finset.mul_sum _ _ _).symm

end StrictEUnit
end
