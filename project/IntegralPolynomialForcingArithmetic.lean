import FiniteForcingArithmeticClosure
import PoleClearedConnectionArithmetic

noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

/-- The actual forcing entry for the cleared scalar source is 1/t in the
last source coordinate, not an arbitrary arithmetic forcing assumption. -/
def sourcePolynomialForcingColumn (r : ℕ) (T : Polynomial (𝓞 K)) :
    Fin r → LaurentSeries K := fun i =>if i.val+1=r then
      (HahnSeries.ofPowerSeries ℤ K ((T.map (algebraMap (𝓞 K) K)) : PowerSeries K))⁻¹ else 0

/-- A nonzero integral clearing polynomial supplies the forcing arithmetic,
including its possible pole at the original center. -/
theorem sourcePolynomialForcingColumn_arithmetic (r : ℕ) (T : Polynomial (𝓞 K))
    (hT : T.map (algebraMap (𝓞 K) K)≠0) :
    LaurentForcingArithmetic (sourcePolynomialForcingColumn r T) := by
  let t := T.map (algebraMap (𝓞 K) K)
  let a := t.natTrailingDegree
  let psi : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  let x := (psi (t : PowerSeries K))⁻¹
  let g := poleClearedPolynomialQuotientGerm t 1 1
  have ht : psi (t : PowerSeries K)≠0 := polynomialLaurentImage_ne_zero t hT
  have hid : psi g=(psi PowerSeries.X)^a*x := by
    have h := congrArg psi (poleClearedPolynomialQuotientGerm_clearing t 1 hT 1)
    simp only [pow_one,Nat.mul_one,Polynomial.coe_one,mul_one,map_mul,map_pow] at h
    change psi (t : PowerSeries K)*psi g=(psi PowerSeries.X)^a at h
    dsimp only [x]
    rw [← div_eq_mul_inv]
    apply (eq_div_iff ht).2
    exact (mul_comm _ _).trans h
  obtain ⟨hq,hq1,hden⟩ := poleClearedPolynomialQuotientGerm_common_denominators
    T (fun (_ : ℕ) (_ : Unit) =>(1 : Polynomial K)) hT 1 le_rfl
    (by intro N
        refine ⟨1,by decide,by simp,?_⟩
        intro m hm i k
        simp only [Nat.cast_one,one_mul,Polynomial.coeff_one]
        split_ifs
        · exact isIntegral_one
        · exact isIntegral_zero)
  let q := Int.natAbs (Algebra.norm ℤ (T.coeff a))
  change 0<q at hq
  change 1≤(q : ℝ)*1 at hq1
  rw [mul_one] at hq1
  have hlow : ∀ l,l< -(a : ℤ) →x.coeff l=0 := by
    intro l hl
    rw [powerSeries_monomial_laurent_coefficient g x a hid l,dif_neg (by omega)]
  refine ⟨a,(q : ℝ)^(a+2),one_le_pow₀ hq1,?_,?_⟩
  · intro i l hl
    dsimp only [sourcePolynomialForcingColumn]
    split_ifs
    · exact hlow l hl
    · rfl
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden (N+a+1)
    refine ⟨D,hD,?_,?_⟩
    · change (D : ℝ)≤((q : ℝ)^(a+2))^(N+1)
      have hb : (D : ℝ)≤(q : ℝ)^(N+a+1+1) := by simpa only [mul_one] using hDb
      apply hb.trans
      rw [← pow_mul]
      apply pow_le_pow_right₀ hq1
      nlinarith
    · intro i l hl
      dsimp only [sourcePolynomialForcingColumn]
      split_ifs
      · change IsIntegral ℤ ((D : K)*x.coeff l)
        rw [powerSeries_monomial_laurent_coefficient g x a hid l]
        split_ifs with ha
        · have hl' : ((a : ℤ)+l).toNat≤a+N := by
            have h := Int.toNat_le_toNat (show (a : ℤ)+l≤((a+N : ℕ) : ℤ) by push_cast;omega)
            simpa only [Int.toNat_natCast] using h
          exact hDi 1 _ (by omega) ()
        · rw [mul_zero]
          exact isIntegral_zero
      · simpa only [HahnSeries.coeff_zero,mul_zero] using (isIntegral_zero : IsIntegral ℤ (0 : K))

end StrictEUnit
end
