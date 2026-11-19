import FiniteForcingArithmeticClosure

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Literal forcing-jet vector: highest forcing derivative first, followed
by the lower forcing derivatives and the unchanged original vector. -/
def polynomialForcingJet {r : ℕ} (P : LaurentSeries K) (y : Fin r → LaurentSeries K) :
    (d : ℕ) → Fin ((r+1)+d) → LaurentSeries K
  | 0 => Fin.cases P y
  | d+1 => Fin.cases
      ((stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P)
      (polynomialForcingJet P y d)

/-- Exact first-row / remaining-row decomposition, even with a nonconstant
external input u in the first row. -/
theorem constantForcingConnection_forced_equations {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b y : Fin r → LaurentSeries K)
    (P u : LaurentSeries K) :
    (∀ i,stage14_laurentAlgebraDerivation (Fin.cases P y i)=
      (∑ j,constantForcingConnection A b i j*Fin.cases P y j)+
        (if i.val=0 then u else 0)) ↔
    stage14_laurentAlgebraDerivation P=u ∧
      ∀ i,stage14_laurentAlgebraDerivation (y i)=(∑ j,A i j*y j)+b i*P := by
  simp only [Fin.forall_fin_succ,Fin.sum_univ_succ,constantForcingConnection,
    Fin.cases_zero,Fin.cases_succ,Fin.val_zero,Fin.val_succ,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false,ite_false,ite_true,zero_mul,Finset.sum_const_zero,
    zero_add,add_zero]
  constructor
  · rintro ⟨h0,hy⟩
    exact ⟨h0,fun i =>(hy i).trans (add_comm _ _)⟩
  · rintro ⟨h0,hy⟩
    exact ⟨h0,fun i =>(hy i).trans (add_comm _ _)⟩

/-- The literal matrix chain acts on its jet exactly as intended. No
arithmetic or solution premise is used to derive this equivalence. -/
theorem polynomialForcingJet_forced_equations {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b y : Fin r → LaurentSeries K)
    (P u : LaurentSeries K) (d : ℕ) :
    (∀ i,stage14_laurentAlgebraDerivation (polynomialForcingJet P y d i)=
      (∑ j,polynomialForcingConnection A b d i j*polynomialForcingJet P y d j)+
        (if i.val=0 then u else 0)) ↔
    (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P=u ∧
      ∀ i,stage14_laurentAlgebraDerivation (y i)=(∑ j,A i j*y j)+b i*P := by
  induction d generalizing u with
  | zero =>simpa only [polynomialForcingConnection,polynomialForcingJet,
      Function.iterate_one] using constantForcingConnection_forced_equations A b y P u
  | succ d ih =>
    rw [polynomialForcingConnection,polynomialForcingJet]
    dsimp only
    refine (constantForcingConnection_forced_equations (polynomialForcingConnection A b d)
      (fun i =>if i.val=0 then 1 else 0) (polynomialForcingJet P y d)
      ((stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P) u).trans ?_
    have hprod : ∀ i : Fin ((r+1)+d),
        (if i.val=0 then (1 : LaurentSeries K) else 0)*
          (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P=
        if i.val=0 then
          (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P else 0 := by
      intro i;split_ifs <;> simp
    simp only [hprod]
    rw [ih]
    simp only [true_and,Function.iterate_succ_apply']

/-- Homogeneous finite-chain solutions on canonical jets are precisely a
source forced by P with D^(d+1)P=0. -/
theorem polynomialForcingJet_solution_iff {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b y : Fin r → LaurentSeries K)
    (P : LaurentSeries K) (d : ℕ) :
    (∀ i,stage14_laurentAlgebraDerivation (polynomialForcingJet P y d i)=
      ∑ j,polynomialForcingConnection A b d i j*polynomialForcingJet P y d j) ↔
    (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P=0 ∧
      ∀ i,stage14_laurentAlgebraDerivation (y i)=(∑ j,A i j*y j)+b i*P := by
  simpa only [ite_self,add_zero] using polynomialForcingJet_forced_equations A b y P 0 d

end StrictEUnit
end
