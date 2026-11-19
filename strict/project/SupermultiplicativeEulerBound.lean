import Mathlib.NumberTheory.EulerProduct.Basic

noncomputable section
open scoped BigOperators
open Nat Finset
namespace StrictEUnit

theorem supermultiplicative_euler_finite_bound {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, m.Coprime n → f m * f n ≤ f (m*n))
    (hsum : Summable f) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (∑' e : ℕ, f (p^e)) ≤ ∑' n : factoredNumbers s, f n := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [factoredNumbers_empty]
    simp only [not_mem_empty, IsEmpty.forall_iff, forall_const, filter_true_of_mem, prod_empty]
    exact le_of_eq (hf1.symm.trans (hasSum_singleton 1 f).tsum_eq.symm)
  | insert p s hp ih =>
    rw [filter_insert]
    split_ifs with hpp
    · rw [prod_insert (fun h => hp (mem_of_mem_filter _ h))]
      have hpS := hsum.comp_injective (Nat.pow_right_injective hpp.one_lt)
      have hsS := hsum.subtype (factoredNumbers s)
      have hmS := hpS.mul_of_nonneg hsS (fun _ => hf _) (fun _ => hf _)
      calc
        _ ≤ (∑' e : ℕ, f (p^e)) * ∑' n : factoredNumbers s, f n :=
          mul_le_mul_of_nonneg_left ih (tsum_nonneg (fun _ => hf _))
        _ = ∑' x : ℕ × factoredNumbers s, f (p^x.1) * f x.2 := hpS.tsum_mul_tsum hsS hmS
        _ ≤ ∑' n : factoredNumbers (insert p s), f n := by
          apply Summable.tsum_le_tsum_of_inj (equivProdNatFactoredNumbers hpp hp)
            (Equiv.injective _) (fun _ _ => hf _) ?_ hmS (hsum.subtype _)
          intro x
          exact hmul ((hpp.factoredNumbers_coprime hp x.2.prop).pow_left x.1)
    · rw [factoredNumbers_insert s hpp]
      exact ih

theorem supermultiplicative_euler_finite_bound_total {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) (hf1 : f 1 = 1)
    (hmul : ∀ {m n}, m.Coprime n → f m * f n ≤ f (m*n))
    (hsum : Summable f) (s : Finset ℕ) :
    ∏ p ∈ s with p.Prime, (∑' e : ℕ, f (p^e)) ≤ ∑' n : ℕ, f n :=
  (supermultiplicative_euler_finite_bound hf hf1 hmul hsum s).trans
    (hsum.tsum_subtype_le _ _ hf)

end StrictEUnit
end
