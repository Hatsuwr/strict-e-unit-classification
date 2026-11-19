import ActualZeroEulerSolution
import ParallelForcingMomentChain

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem finiteLaurentEulerWeights_weighted_constants {r : ℕ}
    (w : Fin r →ℕ) (M : ℕ) (k : ℕ →ℤ) (a : ℕ →K)
    (x : Fin r →LaurentSeries (Polynomial K)) (s : ℕ)
    (hk : ∀ j,j<s →0≤(M:ℤ)+k j) :
    (fun i =>HahnSeries.single (finiteLaurentEulerWeights w M k s i:ℤ) (1:Polynomial K)*
      parallelForcingVector x (fun j =>HahnSeries.single 0 (Polynomial.C (a j))) s i)=
      parallelForcingVector (fun i =>HahnSeries.single (w i:ℤ) (1:Polynomial K)*x i)
        (fun j =>HahnSeries.single ((M:ℤ)+k j) (Polynomial.C (a j))) s := by
  induction s with
  | zero =>rfl
  | succ s ih =>
    funext i
    cases i using Fin.cases with
    | zero =>
      simp only [finiteLaurentEulerWeights,parallelForcingVector,Fin.cases_zero,
        HahnSeries.single_mul_single,add_zero,one_mul]
      rw [Int.toNat_of_nonneg (hk s (Nat.lt_succ_self _))]
    | succ i =>exact congrFun (ih (fun j hj =>hk j (Nat.lt_succ_of_lt hj))) i

/-- Actual reflected forcing coordinates, after the proved gauge, have precisely
the distinct residual eigenvalues needed by the moment companion construction. -/
theorem reflectedResidual_weighted_parallel_moments (n d : ℕ) (T : Polynomial K)
    (P : Polynomial K) (x : Fin (n+1) →LaurentSeries (Polynomial K)) :
    let s := P.natDegree+1
    let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
    let M := finiteLaurentOffset k s
    let w := finiteLaurentEulerWeights (fun i =>M+T.natTrailingDegree+i.val) (M+(n+1)) k s
    let a := fun j : ℕ =>(-1:K)^(k j)*P.coeff j
    let h := fun j : ℕ =>HahnSeries.single (((M+(n+1):ℕ):ℤ)+k j) (Polynomial.C (a j))
    let lam := fun j : Fin s =>((((M+(n+1):ℕ):ℤ)+(d:ℤ)-(j.val:ℤ):ℤ):K)
    (fun i =>HahnSeries.single (w i:ℤ) (1:Polynomial K)*
      parallelForcingVector x (reflectedResidualConstant d P) s i)=
        parallelForcingVector (fun i =>HahnSeries.single ((M+T.natTrailingDegree+i.val:ℕ):ℤ)
          (1:Polynomial K)*x i) h s ∧
    (forcingMomentMatrix lam).det≠0 ∧
    ∃ b : Fin s →K,
      (∀ m,polynomialCoefficientEuler 1 (forcingMoment lam (fun j =>h j.val) m)=
        forcingMoment lam (fun j =>h j.val) (m+1)) ∧
      forcingMoment lam (fun j =>h j.val) s=
        ∑ m : Fin s,b m • forcingMoment lam (fun j =>h j.val) m.val ∧
      forcingMoment lam (fun j =>h j.val) 0=∑ j : Fin s,h j.val := by
  intro s k M w a h lam
  constructor
  · apply finiteLaurentEulerWeights_weighted_constants
    intro j hj
    have he := finiteLaurentOffset_nonnegative k s j hj
    change 0≤((finiteLaurentOffset k s+(n+1):ℕ):ℤ)+k j
    push_cast
    omega
  · apply residualForcing_moment_chain s ((M+(n+1):ℕ):ℤ) (d:ℤ) (fun j =>h j.val)
    intro j
    dsimp only [h,k]
    rw [coefficientEuler_constant_monomial]
    congr 1
    push_cast
    ring

end StrictEUnit
end
