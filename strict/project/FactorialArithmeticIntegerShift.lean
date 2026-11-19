import ActualAmplitudeFactorialArithmetic
import FourierLaurentRealization

noncomputable section
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

theorem factorialLogPrefixArithmetic_shift_one (p : Polynomial (LaurentSeries K))
    (hp : FactorialLogPrefixArithmetic p) : FactorialLogPrefixArithmetic (frobeniusIntegerShift 1 p) := by
  obtain ⟨B,hB,hden⟩ := hp
  let f : Unit →ℤ →Polynomial K := fun _ z =>
    (z.toNat.factorial:K) • (logPolynomialToCoefficientSeries (frobeniusIntegerShift 1 p)).coeff z
  obtain ⟨A,hA,hAd⟩ := logPolynomial_tail_to_prefix f 1 B hB (by
    intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hden N
    refine ⟨D,hD,hDb,?_⟩
    intro m hm i t
    dsimp only [f]
    rw [Polynomial.coeff_smul,smul_eq_mul,logPolynomialToCoefficientSeries_double_coeff,
      frobeniusIntegerShift_coeff,add_sub_cancel_right]
    have he : ((m:ℤ)+1).toNat=m+1 := by omega
    rw [he,Nat.factorial_succ,Nat.cast_mul]
    convert (ordinaryJet_natCast_integral (K:=K) (m+1)).mul (hDi m hm t) using 1 <;> ring)
  refine ⟨A,hA,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hAd N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm t
  have hi := hDi m hm () t
  simpa only [f,Int.toNat_natCast,Polynomial.coeff_smul,smul_eq_mul,
    logPolynomialToCoefficientSeries_double_coeff,mul_assoc] using hi

theorem factorialLogPrefixArithmetic_shift_neg_one (p : Polynomial (LaurentSeries K))
    (hp : FactorialLogPrefixArithmetic p) : FactorialLogPrefixArithmetic (frobeniusIntegerShift (-1) p) := by
  obtain ⟨B,hB,hden⟩ := hp
  refine ⟨B^2*16,by nlinarith [sq_nonneg (B-1)],fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden (N+1)
  let Q := logJetLCM (N+1)
  refine ⟨D*Q,Nat.mul_pos hD (logJetLCM_pos _),?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    apply mul_le_mul ?_ (logJetLCM_real_le_sixteen_pow (N+1)) (by positivity) (by positivity)
    calc
      (D:ℝ) ≤ B^(N+1+1) := hDb
      _ ≤ B^(2*(N+1)) := pow_le_pow_right₀ hB (by omega)
      _ = (B^2)^(N+1) := pow_mul B 2 (N+1)
  intro m hm t
  rw [frobeniusIntegerShift_coeff]
  have he : (m:ℤ)-(-1)=((m+1:ℕ):ℤ) := by omega
  rw [he]
  have hquot : IsIntegral ℤ ((Q:K)/(m+1:ℕ)) :=
    integral_nat_quotient_of_dvd Q (m+1) (by omega) (logJetLCM_dvd (N+1) (m+1) (by omega) (by omega))
  have hi := hquot.mul (hDi (m+1) (by omega) t)
  convert hi using 1
  rw [Nat.cast_mul,Nat.factorial_succ,Nat.cast_mul]
  have hm0 : ((m+1:ℕ):K)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hm1 : (m:K)+1≠0 := by exact_mod_cast Nat.succ_ne_zero m
  push_cast
  field_simp [hm1]
  <;> ring

theorem factorialLogPrefixArithmetic_integer_shift (p : Polynomial (LaurentSeries K))
    (hp : FactorialLogPrefixArithmetic p) (z : ℤ) :
    FactorialLogPrefixArithmetic (frobeniusIntegerShift z p) := by
  induction z using Int.induction_on with
  | hz => simpa [frobeniusIntegerShift] using hp
  | hp k ih =>
    have h := factorialLogPrefixArithmetic_shift_one _ ih
    rw [frobeniusIntegerShift_add] at h
    simpa only [add_comm] using h
  | hn k ih =>
    have h := factorialLogPrefixArithmetic_shift_neg_one _ ih
    rw [frobeniusIntegerShift_add] at h
    convert h using 1 <;> congr 1 <;> omega
end StrictEUnit
end
