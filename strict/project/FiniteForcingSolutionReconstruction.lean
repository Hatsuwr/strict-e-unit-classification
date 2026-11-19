import FiniteForcingJetSolutions

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- No coordinates are lost in the recursive first-coordinate decomposition. -/
theorem finiteForcing_vector_decomposition {r : ℕ} (v : Fin (r+1) → LaurentSeries K) :
    v=Fin.cases (v 0) (fun i =>v i.succ) := by
  funext i
  exact Fin.cases rfl (fun j =>rfl) i

/-- Every solution of the literal finite chain, not only a canonical ansatz,
reconstructs its forcing polynomial jet and original source vector. -/
theorem polynomialForcing_reconstruct_solution {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (d : ℕ) (v : Fin ((r+1)+d) → LaurentSeries K) (u : LaurentSeries K)
    (hv : ∀ i,stage14_laurentAlgebraDerivation (v i)=
      (∑ j,polynomialForcingConnection A b d i j*v j)+(if i.val=0 then u else 0)) :
    ∃ P y,v=polynomialForcingJet P y d ∧
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P=u ∧
      ∀ i,stage14_laurentAlgebraDerivation (y i)=(∑ j,A i j*y j)+b i*P := by
  induction d generalizing u with
  | zero =>
    have heq := finiteForcing_vector_decomposition v
    have h := hv
    rw [heq] at h
    obtain ⟨hP,hy⟩ := (constantForcingConnection_forced_equations A b (fun i =>v i.succ) (v 0) u).mp h
    exact ⟨v 0,fun i =>v i.succ,heq,hP,hy⟩
  | succ d ih =>
    have heq := finiteForcing_vector_decomposition v
    have h := hv
    rw [heq] at h
    obtain ⟨hc,hw⟩ := (constantForcingConnection_forced_equations (polynomialForcingConnection A b d)
      (fun i =>if i.val=0 then 1 else 0) (fun i =>v i.succ) (v 0) u).mp h
    have hw' : ∀ i,stage14_laurentAlgebraDerivation (v i.succ)=
        (∑ j,polynomialForcingConnection A b d i j*v j.succ)+(if i.val=0 then v 0 else 0) := by
      intro i
      simpa only [ite_mul,one_mul,zero_mul] using hw i
    obtain ⟨P,y,hy,hP,hs⟩ := ih _ _ hw'
    refine ⟨P,y,?_,?_,hs⟩
    · calc
        v=Fin.cases (v 0) (fun i =>v i.succ) := heq
        _=polynomialForcingJet P y (d+1) := by
          funext i
          refine Fin.cases ?_ (fun j =>?_) i
          · exact hP.symm
          · exact congrFun hy j
    · rw [Function.iterate_succ_apply',hP]
      exact hc

/-- Exact all-vector equivalence for the homogeneous finite forcing chain. -/
theorem polynomialForcing_solution_iff_exists_jet {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (LaurentSeries K)) (b : Fin r → LaurentSeries K)
    (d : ℕ) (v : Fin ((r+1)+d) → LaurentSeries K) :
    (∀ i,stage14_laurentAlgebraDerivation (v i)=
      ∑ j,polynomialForcingConnection A b d i j*v j) ↔
    ∃ P y,v=polynomialForcingJet P y d ∧
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1] P=0 ∧
      ∀ i,stage14_laurentAlgebraDerivation (y i)=(∑ j,A i j*y j)+b i*P := by
  constructor
  · intro hv
    apply polynomialForcing_reconstruct_solution A b d v 0
    simpa only [ite_self,add_zero] using hv
  · rintro ⟨P,y,rfl,hP,hy⟩
    exact (polynomialForcingJet_solution_iff A b y P d).mpr ⟨hP,hy⟩

end StrictEUnit
end
