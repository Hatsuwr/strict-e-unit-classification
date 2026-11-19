import ResidueExponentRationality

noncomputable section
open scoped BigOperators
namespace StrictEUnit

/-- One positive natural ramification clears every member of a finite rational
family, including the empty family (where the product is one). -/
theorem finite_rational_exponent_ramification {ι : Type*} [Fintype ι]
    (r : ι → ℚ) : ∃ N : ℕ, 0 < N ∧ ∃ z : ι → ℤ, ∀ i, (N : ℚ) * r i = z i := by
  classical
  let N := ∏ i, (r i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hd : ∀ i, (r i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  choose k hk using hd
  refine ⟨N,hN,fun i => (k i : ℤ) * (r i).num,?_⟩
  intro i
  rw [hk i, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  have hd0 : ((r i).den : ℚ) ≠ 0 := by exact_mod_cast (r i).den_ne_zero
  conv_lhs => rhs; rw [← (r i).num_div_den]
  field_simp [hd0]
  <;> ring

/-- A joint arithmetic family now has rational witnesses and one actual
positive ramification converting every external exponent into an integer. -/
theorem jointBinomialPrefixDenominators_rational_ramification
    {ι : Type*} [Fintype ι] (rho : ι → AlgebraicComplex)
    (h : JointBinomialPrefixDenominators rho) :
    ∃ r : ι → ℚ, (∀ i, algebraMap ℚ AlgebraicComplex (r i) = rho i) ∧
      ∃ N : ℕ, 0 < N ∧ ∃ z : ι → ℤ,
        ∀ i, (N : AlgebraicComplex) * rho i = (z i : AlgebraicComplex) := by
  have hi : ∀ i, BinomialPrefixDenominators (rho i) := by
    intro i
    obtain ⟨C,hC,hden⟩ := h
    refine ⟨C,hC,?_⟩
    intro n
    obtain ⟨d,hd,hdb,hdi⟩ := hden n
    exact ⟨d,hd,hdb,fun m hm => hdi m hm i⟩
  choose r hr using fun i => algebraicComplex_binomialPrefixDenominators_rational (rho i) (hi i)
  obtain ⟨N,hN,z,hz⟩ := finite_rational_exponent_ramification r
  refine ⟨r,hr,N,hN,z,?_⟩
  intro i
  rw [← hr i]
  have hh := congrArg (algebraMap ℚ AlgebraicComplex) (hz i)
  simpa using hh

end StrictEUnit
end
