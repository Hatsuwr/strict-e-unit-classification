import FactorialArithmeticIntegerShift
import RetainedFactorialArithmetic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K]

theorem factorialLogPrefixArithmetic_map (phi : K →+* L)
    (p : Polynomial (LaurentSeries K)) (hp : FactorialLogPrefixArithmetic p) :
    FactorialLogPrefixArithmetic (stage38_logMap phi p) := by
  obtain ⟨B,hB,hden⟩ := hp
  refine ⟨B,hB,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro n hn t
  have hi := (hDi n hn t).map phi.toIntAlgHom
  simpa only [RingHom.toIntAlgHom_apply,map_mul,map_natCast,stage38_logMap_coeff] using hi

theorem finite_factorialLogPrefixArithmetic {ι : Type*} [Fintype ι]
    (p : ι →Polynomial (LaurentSeries K)) (hp : ∀ i,FactorialLogPrefixArithmetic (p i)) :
    ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D:ℝ)≤B^(N+1) ∧
      ∀ i n,n≤N →∀ t,IsIntegral ℤ ((D:K)*(n.factorial:K)*((p i).coeff t).coeff (n:ℤ)) := by
  classical
  choose B hB hden using hp
  refine ⟨∏ i,B i,?_,fun N =>?_⟩
  · simpa using (Finset.prod_le_prod (s:=Finset.univ)
      (f:=fun _ : ι => (1:ℝ)) (g:=B) (fun _ _ =>zero_le_one) (fun i _ =>hB i))
  choose D hD hDb hDi using (fun i =>hden i N)
  refine ⟨∏ i,D i,Finset.prod_pos (fun i _ =>hD i),?_,?_⟩
  · rw [Nat.cast_prod]
    exact (Finset.prod_le_prod (fun i _ =>Nat.cast_nonneg (D i))
      (fun i _ =>hDb i)).trans_eq (Finset.prod_pow Finset.univ (N+1) B)
  intro i n hn t
  obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  rw [hb,Nat.cast_mul]
  convert (ordinaryJet_natCast_integral (K:=K) b).mul (hDi i n hn t) using 1 <;> ring
end StrictEUnit
end
