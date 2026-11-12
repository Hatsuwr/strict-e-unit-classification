import FiniteLogSystemScalarODE

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A solved finite-order twisted scalar equation gives a genuine ordinary
polynomial ODE for each log coefficient. All intermediate jets are retained. -/
theorem twistedScalarJet_coefficient_polynomialODE
    (rho : K) (p : Polynomial (LaurentSeries K)) (n : ℕ)
    (c : Fin (n+1) → RatFunc K)
    (h : (actualTwistedLogOrdinary rho)^[n+1] p =
      ∑ j,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (c j))*
        (actualTwistedLogOrdinary rho)^[j.val] p) :
    ∀ j,HasPolynomialScalarDifferentialRelation (k:=K)
      stage14_laurentAlgebraDerivation (p.coeff j) := by
  classical
  let y (i : Fin (n+1)) := (actualTwistedLogOrdinary rho)^[i.val] p
  let C : Matrix (Fin (n+1)) (Fin (n+1)) (RatFunc K) := fun i j =>
    if i.val=n then c j else if j.val=i.val+1 then 1 else 0
  have hy (i : Fin (n+1)) : actualTwistedLogOrdinary rho (y i)=
      ∑ j,Polynomial.C (algebraMap (RatFunc K) (LaurentSeries K) (C i j))*y j := by
    by_cases hi : i.val=n
    · simpa only [y,C,hi,if_pos,← Function.iterate_succ_apply'] using h
    · let k : Fin (n+1) := ⟨i.val+1,by omega⟩
      have he (j : Fin (n+1)) : (j.val=i.val+1) ↔ j=k := by
        constructor
        · intro hj;apply Fin.ext;exact hj
        · intro hj;subst j;rfl
      simp only [C,hi,if_false,he]
      simp only [apply_ite,map_one,map_zero,ite_mul,one_mul,zero_mul,
        Finset.sum_ite_eq',Finset.mem_univ,if_true]
      exact (Function.iterate_succ_apply' _ i.val p).symm
  let d := Finset.univ.sup (fun i =>(y i).natDegree)
  have hd (i : Fin (n+1)) : (y i).natDegree≤d := Finset.le_sup (f:=fun i =>(y i).natDegree) (Finset.mem_univ i)
  have hr := finiteTwistedLogSystem_coefficient_polynomialODE rho C y d hd hy (0:Fin (n+1))
  simpa only [y,Fin.val_zero,Function.iterate_zero, id_eq] using hr
end StrictEUnit
end
