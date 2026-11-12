import Stage38SeriesCoefficientExtension

/-!
# Positive integral ramification of actual finite-log Laurent series

The substitution is t ↦ t^N and ell ↦ ell, with coefficients retained.
It is an injective algebra homomorphism on K((t))[ell]. Its differential
compatibility below uses ell = log z, so the logarithmic symbol is not scaled.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
namespace StrictEUnit
variable {K ι : Type*} [Field K]

/-- Multiplication of integer exponents, bundled additively. -/
def stage38_exponentScale (N : ℕ) : ℤ →+ ℤ where
  toFun n := (N : ℤ) * n
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

theorem stage38_exponentScale_injective (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage38_exponentScale N) := by
  intro a b h
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hN) h

theorem stage38_exponentScale_le (N : ℕ) (hN : N ≠ 0) (a b : ℤ) :
    stage38_exponentScale N a ≤ stage38_exponentScale N b ↔ a ≤ b :=
  mul_le_mul_left (by exact_mod_cast Nat.pos_of_ne_zero hN)

/-- Literal substitution in arbitrary formal Laurent series. -/
def stage38_laurentRamification (N : ℕ) (hN : N ≠ 0) :
    LaurentSeries K →ₐ[K] LaurentSeries K :=
  { HahnSeries.embDomainRingHom (stage38_exponentScale N)
      (stage38_exponentScale_injective N hN) (stage38_exponentScale_le N hN) with
    commutes' := fun c => by
      simp only [LaurentSeries.algebraMap_apply]
      exact HahnSeries.embDomainRingHom_C }

@[simp] theorem stage38_laurentRamification_coeff (N : ℕ) (hN : N ≠ 0)
    (x : LaurentSeries K) (n : ℤ) :
    (stage38_laurentRamification N hN x).coeff ((N : ℤ) * n) = x.coeff n :=
  HahnSeries.embDomain_coeff

theorem stage38_laurentRamification_coeff_outside (N : ℕ) (hN : N ≠ 0)
    (x : LaurentSeries K) (n : ℤ) (hn : n ∉ Set.range (stage38_exponentScale N)) :
    (stage38_laurentRamification N hN x).coeff n = 0 :=
  HahnSeries.embDomain_notin_range hn

theorem stage38_laurentRamification_injective (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage38_laurentRamification (K := K) N hN) :=
  HahnSeries.embDomain_injective

/-- The finite-log extension fixes the logarithmic indeterminate. -/
def stage38_logRamification (N : ℕ) (hN : N ≠ 0) :
    Polynomial (LaurentSeries K) →ₐ[K] Polynomial (LaurentSeries K) :=
  Polynomial.mapAlgHom (stage38_laurentRamification N hN)

@[simp] theorem stage38_logRamification_coeff (N : ℕ) (hN : N ≠ 0)
    (p : Polynomial (LaurentSeries K)) (j : ℕ) :
    (stage38_logRamification N hN p).coeff j =
      stage38_laurentRamification N hN (p.coeff j) :=
  Polynomial.coeff_map _ _

theorem stage38_logRamification_injective (N : ℕ) (hN : N ≠ 0) :
    Function.Injective (stage38_logRamification (K := K) N hN) :=
  Polynomial.map_injective _ (stage38_laurentRamification_injective N hN)

/-- Positive ramification preserves independence over the unchanged constant field. -/
theorem stage38_logRamification_linearIndependent (N : ℕ) (hN : N ≠ 0)
    (v : ι → Polynomial (LaurentSeries K)) (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => stage38_logRamification N hN (v i)) :=
  by
    have hv' : @LinearIndependent ι K (Polynomial (LaurentSeries K)) v _ _
        (Algebra.toModule : Module K (Polynomial (LaurentSeries K))) := by
      simpa only [stage38_logModule_eq] using hv
    have h := stage38_algHom_linearIndependent (stage38_logRamification N hN)
      (stage38_logRamification_injective N hN) v hv'
    simpa only [stage38_logModule_eq] using h

/-- The unnormalized Euler-log operator scales by N under t ↦ t^N.
The source log coefficient d becomes N*d; ell itself stays unchanged. -/
theorem stage38_logRamification_euler (N : ℕ) (hN : N ≠ 0) (d : K)
    (p : Polynomial (LaurentSeries K)) :
    logPolynomialEuler ((N : K) * d) (stage38_logRamification N hN p) =
      Polynomial.C (HahnSeries.single (0 : ℤ) (N : K)) *
        stage38_logRamification N hN (logPolynomialEuler d p) := by
  apply Polynomial.ext
  intro j
  apply HahnSeries.ext
  funext n
  rw [Polynomial.coeff_C_mul]
  have hmul (x : LaurentSeries K) :
      (HahnSeries.single (0 : ℤ) (N : K) * x).coeff n = (N : K) * x.coeff n := by
    simpa only [add_zero] using (HahnSeries.coeff_single_mul_add
      (a := n) (b := (0 : ℤ)) (r := (N : K)) (x := x))
  rw [hmul]
  by_cases hn : n ∈ Set.range (stage38_exponentScale N)
  · obtain ⟨a, rfl⟩ := hn
    simp only [logPolynomialEuler_double_coeff, stage38_logRamification_coeff]
    change (((N : ℤ) * a : ℤ) : K) *
      (stage38_laurentRamification N hN (p.coeff j)).coeff ((N : ℤ) * a) +
      (N : K) * d * ((stage38_laurentRamification N hN (p.coeff (j+1))).coeff
        ((N : ℤ) * a) * (j+1 : K)) =
      (N : K) * (stage38_laurentRamification N hN
        ((logPolynomialEuler d p).coeff j)).coeff ((N : ℤ) * a)
    rw [stage38_laurentRamification_coeff, stage38_laurentRamification_coeff,
      stage38_laurentRamification_coeff, logPolynomialEuler_double_coeff]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  · simp only [logPolynomialEuler_double_coeff, stage38_logRamification_coeff,
      stage38_laurentRamification_coeff_outside N hN _ n hn, mul_zero, zero_mul, add_zero]

end StrictEUnit
