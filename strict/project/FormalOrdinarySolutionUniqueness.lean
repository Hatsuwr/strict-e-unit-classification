import OrdinaryAnalyticODETransfer
import Mathlib.Algebra.BigOperators.NatAntidiagonal

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit

/-- Formal ordinary systems have unique solutions for supplied initial values.
No convergence or arithmetic property is supplied to this uniqueness theorem. -/
theorem powerSeries_system_solution_unique
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (B : Matrix (Fin r) (Fin r) (PowerSeries K))
    (v w : Fin r → PowerSeries K)
    (hv : ∀ i, PowerSeries.derivative K (v i) = ∑ l,B i l*v l)
    (hw : ∀ i, PowerSeries.derivative K (w i) = ∑ l,B i l*w l)
    (h0 : ∀ i, PowerSeries.constantCoeff K (v i) = PowerSeries.constantCoeff K (w i)) :
    v=w := by
  classical
  have hc : ∀ n i, PowerSeries.coeff K n (v i) = PowerSeries.coeff K n (w i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i
      cases n with
      | zero => simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using h0 i
      | succ n =>
        have hvn := congrArg (PowerSeries.coeff K n) (hv i)
        have hwn := congrArg (PowerSeries.coeff K n) (hw i)
        simp only [PowerSeries.coeff_derivative,map_sum,PowerSeries.coeff_mul] at hvn hwn
        have hs : (∑ l,∑ p ∈ Finset.antidiagonal n,
            PowerSeries.coeff K p.1 (B i l)*PowerSeries.coeff K p.2 (v l)) =
            ∑ l,∑ p ∈ Finset.antidiagonal n,
              PowerSeries.coeff K p.1 (B i l)*PowerSeries.coeff K p.2 (w l) := by
          apply Finset.sum_congr rfl
          intro l hl
          apply Finset.sum_congr rfl
          intro p hp
          have hp' := Finset.mem_antidiagonal.1 hp
          rw [ih p.2 (by omega) l]
        have he := hvn.trans (hs.trans hwn.symm)
        exact mul_right_cancel₀ (by exact_mod_cast (Nat.succ_ne_zero n) : (n+1:K) ≠ 0) he
  funext i
  exact PowerSeries.ext (fun n => hc n i)

/-- Multiplying a formal solution frame by constant initial data gives a
solution of the literal same left matrix system. -/
theorem powerSeries_frame_constant_combination_solution
    {K : Type*} [Field K] {r : ℕ}
    (B Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hZ : Z.map (PowerSeries.derivative K)=B*Z) (c : Fin r → K) :
    ∀ i, PowerSeries.derivative K (∑ j,Z i j*PowerSeries.C K (c j)) =
      ∑ l,B i l*(∑ j,Z l j*PowerSeries.C K (c j)) := by
  classical
  intro i
  have hz (i j : Fin r) : PowerSeries.derivative K (Z i j) = ∑ l,B i l*Z l j := by
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j) hZ
    exact h
  rw [map_sum]
  simp only [Derivation.leibniz,PowerSeries.derivative_C,smul_eq_mul,mul_zero,zero_add,hz]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem powerSeries_frame_constant_combination_zero
    {K : Type*} [Field K] {r : ℕ}
    (Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hZ0 : Z.map (PowerSeries.constantCoeff K)=1) (c : Fin r → K) :
    ∀ i, PowerSeries.constantCoeff K (∑ j,Z i j*PowerSeries.C K (c j))=c i := by
  classical
  intro i
  have hz (i j : Fin r) : PowerSeries.constantCoeff K (Z i j) = if i=j then 1 else 0 := by
    simpa only [Matrix.map_apply,Matrix.one_apply] using congrArg
      (fun M : Matrix (Fin r) (Fin r) K => M i j) hZ0
  simp only [map_sum,map_mul,PowerSeries.constantCoeff_C,hz]
  simp

/-- Every formal germ of the same ordinary system is the actual normalized
frame times its own initial vector; no representation premise is assumed. -/
theorem powerSeries_solution_eq_frame_initial
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (B Z : Matrix (Fin r) (Fin r) (PowerSeries K))
    (hZ : Z.map (PowerSeries.derivative K)=B*Z)
    (hZ0 : Z.map (PowerSeries.constantCoeff K)=1)
    (v : Fin r → PowerSeries K)
    (hv : ∀ i,PowerSeries.derivative K (v i)=∑ l,B i l*v l) :
    ∀ i,v i=∑ j,Z i j*PowerSeries.C K (PowerSeries.constantCoeff K (v j)) := by
  have he := powerSeries_system_solution_unique B v
    (fun i => ∑ j,Z i j*PowerSeries.C K (PowerSeries.constantCoeff K (v j))) hv
    (powerSeries_frame_constant_combination_solution B Z hZ (fun j => PowerSeries.constantCoeff K (v j)))
    (fun i => (powerSeries_frame_constant_combination_zero Z hZ0 (fun j => PowerSeries.constantCoeff K (v j)) i).symm)
  exact congrFun he

end StrictEUnit
end
