import FocusedFourierNormalizationCore
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
theorem connection_iterate_leibniz (d : Derivation K A A)
    (D : A →ₗ[K] A) (hd : ∀ x y,D (x*y)=d x*y+x*D y)
    (n : ℕ) (p q : A) :
    (D : A → A)^[n] (p * q) =
      ∑ k ∈ Finset.range n.succ,
        n.choose k • ((d : A → A)^[n-k] p * (D : A → A)^[k] q) := by
  induction n with
  | zero => simp [Finset.range]
  | succ n ih =>
    calc
      (D : A → A)^[n+1] (p*q) = D
          (∑ k ∈ Finset.range n.succ,
            n.choose k • ((d : A → A)^[n-k] p * (D : A → A)^[k] q)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k+1] p * (D : A → A)^[k] q)) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (D : A → A)^[k+1] q) := by
        simp_rw [map_sum, map_nsmul, hd, Function.iterate_succ_apply',
          smul_add, Finset.sum_add_distrib]
      _ = (∑ k ∈ Finset.range n.succ,
          n.choose k.succ • ((d : A → A)^[n-k] p * (D : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (D : A → A)^[0] q) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (D : A → A)^[k+1] q) := by
        congr 1
        refine (Finset.sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
        · rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.mem_range] at hk
          congr
          omega
        · rw [Nat.choose_zero_right, tsub_zero]
      _ = ((∑ k ∈ Finset.range n.succ,
          n.choose k • ((d : A → A)^[n-k] p * (D : A → A)^[k+1] q)) +
          ∑ k ∈ Finset.range n.succ,
          n.choose k.succ • ((d : A → A)^[n-k] p * (D : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (D : A → A)^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ k ∈ Finset.range n.succ,
          (n+1).choose (k+1) •
            ((d : A → A)^[n+1-(k+1)] p * (D : A → A)^[k+1] q)) +
          1 • ((d : A → A)^[n+1] p * (D : A → A)^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ,
          add_smul, Finset.sum_add_distrib]
      _ = _ := by
        rw [Finset.sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]


end StrictEUnit
end
