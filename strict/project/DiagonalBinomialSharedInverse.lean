import DiagonalBinomialEndpoint

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- One integer clears every NONZERO diagonal inverse through the cutoff.
This is stronger than individual pivot bounds, but not an arbitrary mixed
upper/lower-index estimate and not a rule for inverting zero pivots. -/
def DiagonalBinomialInversePrefixDenominators (x : K) : Prop :=
  ∃ C : ℝ,1≤C ∧ ∀ N : ℕ,∃ e : ℕ,0<e ∧ (e : ℝ)≤C^(N+1) ∧
    ∀ n,n≤N → Ring.choose (x+(n : K)) n≠0 →
      IsIntegral ℤ ((e : K)*(Ring.choose (x+(n : K)) n)⁻¹)

/-- The fixed-endpoint proof genuinely places e before every n≤N. -/
theorem noninteger_diagonalBinomial_shared_inverse (x : K)
    (hx : BinomialPrefixDenominators x) (hni : ∀ z : ℤ,x≠(z : K)) :
    DiagonalBinomialInversePrefixDenominators x := by
  have hj : JointBinomialPrefixDenominators (fun _ : Unit => x) :=
    finite_binomialPrefixDenominators _ (fun _ => hx)
  obtain ⟨A,hA,hInv⟩ := binomialCompositeValue_individual_inverse_bounds
    (fun _ : Unit => x) hj 1
  obtain ⟨B,hB,hden⟩ := hx
  refine ⟨A*B*16,one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hB) (by norm_num),?_⟩
  intro N
  have hend := diagonal_choose_nonzero_of_noninteger x hni N
  have hp : binomialCompositeValue (fun _ : Unit => x) (fun _ : Fin 1 => ()) (fun _ => N) N≠0 := by
    simpa only [binomialCompositeValue,Fin.prod_univ_one] using hend
  obtain ⟨e,he,heb,hei⟩ := hInv N N le_rfl (fun _ => ()) (fun _ => N) (fun _ => le_rfl) hp
  simp only [binomialCompositeValue,Fin.prod_univ_one] at hei
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨e*D*logJetLCM N,mul_pos (mul_pos he hD) (logJetLCM_pos N),?_,?_⟩
  · simp only [Nat.cast_mul,mul_pow]
    apply mul_le_mul
    · exact mul_le_mul heb hDb (Nat.cast_nonneg _) (pow_nonneg (le_trans zero_le_one hA) _)
    · exact (logJetLCM_real_le_sixteen_pow N).trans (pow_le_pow_right₀ (by norm_num) (Nat.le_succ _))
    · exact Nat.cast_nonneg _
    · exact mul_nonneg (pow_nonneg (le_trans zero_le_one hA) _) (pow_nonneg (le_trans zero_le_one hB) _)
  · intro n hn hne
    have htop : IsIntegral ℤ ((D : K)*Ring.choose (x+(N : K)) (N-n)) :=
      binomial_nat_translate_cleared x D N
        (by intro m hm;rw [field_choose_eq_descPochhammer_div];exact hDi m hm) N (N-n) (Nat.sub_le _ _)
    have hnat : IsIntegral ℤ ((logJetLCM N : K)*((N.choose n : ℕ) : K)⁻¹) := by
      simpa only [div_eq_mul_inv] using integral_nat_quotient_of_dvd (K:=K)
        _ _ (Nat.choose_pos hn) (nat_choose_dvd_logJetLCM N N n le_rfl hn)
    rw [diagonal_choose_inverse_from_endpoint x N n hn hend]
    convert (hei.mul htop).mul hnat using 1 <;> push_cast <;> ring

/-- Integer offsets, including negative collisions, use the shared LCM
instead of a possibly zero endpoint. Only the genuinely nonzero terms enter. -/
theorem integer_diagonalBinomial_shared_inverse (z : ℤ) :
    DiagonalBinomialInversePrefixDenominators (z : K) := by
  refine ⟨(16 : ℝ)^(z.natAbs+2),one_le_pow₀ (by norm_num),?_⟩
  intro N
  refine ⟨logJetLCM (2*N+z.natAbs),logJetLCM_pos _,?_,?_⟩
  · apply (logJetLCM_real_le_sixteen_pow _).trans
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    have hpos : 0≤z.natAbs*N := Nat.zero_le _
    nlinarith
  · intro n hn hne
    have hsize : (z+(n : ℤ)).natAbs+n≤2*N+z.natAbs := by
      have h := Int.natAbs_add_le z (n : ℤ)
      simp only [Int.natAbs_natCast] at h
      omega
    simpa only [Int.cast_add,Int.cast_natCast] using
      resonance_integer_choose_inverse_lcm (K:=K) (2*N+z.natAbs) (z+(n : ℤ)) n hsize
        (by simpa only [Int.cast_add,Int.cast_natCast] using hne)

/-- Every binomial-arithmetic algebraic exponent has common exponential
NONZERO diagonal inverse denominators, with no rationality or class premise. -/
theorem diagonalBinomial_shared_inverse (x : K) (hx : BinomialPrefixDenominators x) :
    DiagonalBinomialInversePrefixDenominators x := by
  classical
  by_cases hi : ∃ z : ℤ,x=(z : K)
  · obtain ⟨z,rfl⟩ := hi
    exact integer_diagonalBinomial_shared_inverse z
  · exact noninteger_diagonalBinomial_shared_inverse x hx (by simpa using hi)

end StrictEUnit
end
