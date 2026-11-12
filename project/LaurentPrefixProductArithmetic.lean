import IntegerBinomialSharedInverse
import LaurentDiagonalGaugeArithmetic

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Literal Laurent convolution, with explicit lower support bounds. -/
theorem forcing_laurent_product_integral (x y : LaurentSeries K) (a b L : ℤ)
    (Dx Dy : K) (hxlow : ∀ j,j<a →x.coeff j=0) (hylow : ∀ j,j<b →y.coeff j=0)
    (hx : ∀ j,j≤L-b →IsIntegral ℤ (Dx*x.coeff j))
    (hy : ∀ j,j≤L-a →IsIntegral ℤ (Dy*y.coeff j)) :
    ∀ l,l≤L →IsIntegral ℤ (Dx*Dy*(x*y).coeff l) := by
  intro l hl
  rw [HahnSeries.coeff_mul,Finset.mul_sum]
  apply IsIntegral.sum
  rintro ⟨i,j⟩ hij
  have hs := Finset.mem_addAntidiagonal.mp hij
  have hix : x.coeff i≠0 := hs.1
  have hjy : y.coeff j≠0 := hs.2.1
  have hi : a ≤ i := by by_contra h;exact hix (hxlow i (by omega))
  have hj : b ≤ j := by by_contra h;exact hjy (hylow j (by omega))
  have he : i+j=l := hs.2.2
  convert (hx i (by omega)).mul (hy j (by omega)) using 1 <;> ring

theorem forcing_laurent_product_lower (x y : LaurentSeries K) (a b : ℤ)
    (hx : ∀ j,j<a →x.coeff j=0) (hy : ∀ j,j<b →y.coeff j=0) :
    ∀ l,l<a+b →(x*y).coeff l=0 := by
  intro l hl
  rw [HahnSeries.coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hs := Finset.mem_addAntidiagonal.mp hij
  by_cases hi : i<a
  · rw [hx i hi,zero_mul]
  · rw [hy j (by omega),mul_zero]

/-- Laurent Hasse differentiation only contributes an INTEGER binomial,
even at negative coefficient indices. -/
theorem forcing_laurent_hasse_integral (x : LaurentSeries K) (h : ℕ) (l : ℤ) (D : K)
    (hx : IsIntegral ℤ (D*x.coeff (l+(h : ℤ)))) :
    IsIntegral ℤ (D*(LaurentSeries.hasseDeriv K h x).coeff l) := by
  rw [LaurentSeries.hasseDeriv_coeff,zsmul_eq_mul]
  have hz : IsIntegral ℤ ((Ring.choose (l+(h : ℤ)) h : ℤ) : K) := isIntegral_algebraMap
  convert hx.mul hz using 1 <;> ring

/-- The factorial quotient needed by the forcing extension is cleared by
LCM(N)^2, jointly for every m<=N and every split a<m. -/
theorem forcing_factorial_ratio_lcm_integral (N m a : ℕ) (hm : m≤N) (ha : a<m) :
    IsIntegral ℤ (((logJetLCM N^2 : ℕ) : K)*
      ((a.factorial : K)*((m-1-a).factorial : K)/(m.factorial : K))) := by
  have ham : a≤m := by omega
  have hchoose : IsIntegral ℤ ((logJetLCM N : K)/(m.choose a : K)) :=
    integral_nat_quotient_of_dvd _ _ (Nat.choose_pos ham) (nat_choose_dvd_logJetLCM N m a hm ham)
  have hdiff : IsIntegral ℤ ((logJetLCM N : K)/(m-a : K)) := by
    have h := integral_nat_quotient_of_dvd (K:=K) (logJetLCM N) (m-a) (by omega)
      (logJetLCM_dvd N (m-a) (by omega) (by omega))
    simpa only [Nat.cast_sub ham] using h
  have hf : m.choose a*a.factorial*(m-a).factorial=m.factorial := Nat.choose_mul_factorial_mul_factorial ham
  have he : m-a=(m-1-a)+1 := by omega
  rw [he,Nat.factorial_succ] at hf
  have hfK : (m.choose a : K)*(a.factorial : K)*
      (((m-1-a)+1 : ℕ) : K)*((m-1-a).factorial : K)=(m.factorial : K) := by
    exact_mod_cast (show m.choose a*a.factorial*((m-1-a)+1)*(m-1-a).factorial=m.factorial by simpa only [mul_assoc] using hf)
  have hm0 : (m.factorial : K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have ha0 : (a.factorial : K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a)
  have hh0 : ((m-1-a).factorial : K)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hc0 : (m.choose a : K)≠0 := Nat.cast_ne_zero.mpr (ne_of_gt (Nat.choose_pos ham))
  have hd0 : ((m-a : ℕ) : K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hid : (a.factorial : K)*((m-1-a).factorial : K)/(m.factorial : K)=
      1/((m.choose a : K)*((m-a : ℕ) : K)) := by
    apply (div_eq_div_iff hm0 (mul_ne_zero hc0 hd0)).2
    rw [one_mul]
    calc
      _ = (m.choose a : K)*(a.factorial : K)*(((m-1-a)+1 : ℕ) : K)*((m-1-a).factorial : K) := by
        rw [← he]
        ring
      _ = _ := hfK
  rw [hid]
  convert hchoose.mul hdiff using 1
  rw [Nat.cast_pow,← Nat.cast_sub ham]
  ring

end StrictEUnit
end
