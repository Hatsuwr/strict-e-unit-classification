import V5FiniteRealizationPeriod
import V5MarkedKummerFactor
import V5EntireDomain

noncomputable section
namespace StrictEUnit
variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k] [Algebra k ℂ]

theorem v5KummerEval_period_one (p : LaurentPolynomial k) :
    Function.Periodic (v5KummerEval (algebraMap k ℂ) 1 p) (2 * Real.pi * Complex.I) := by
  intro w
  rw [v5KummerEval_apply, v5KummerEval_apply]
  congr 2
  apply Units.ext
  simp only [v5KummerPoint_val, Nat.cast_one, div_one, Complex.exp_add, Complex.exp_two_pi_mul_I,
    mul_one]

/-- An entire realization over the standard exponential Laurent base yields
a marked Kummer map for any finite algebra. Both the common period and the
monic relations are derived from finiteness. -/
theorem v5_finite_marked_kummer_factor {T : Type*} [CommRing T] [Algebra k T]
    [Algebra (LaurentPolynomial k) T] [Module.Finite (LaurentPolynomial k) T]
    (ρ : T →ₐ[k] v5EntireSubalgebra k)
    (hbase : ∀ b, (ρ (algebraMap (LaurentPolynomial k) T b)).val =
      v5KummerEval (algebraMap k ℂ) 1 b) :
    ∃ (q : ℕ) (_ : 0 < q) (α : T →ₐ[k] LaurentPolynomial k),
      α.toRingHom.comp (algebraMap (LaurentPolynomial k) T) = v5LaurentPower q ∧
      (∀ x, v5KummerEval (algebraMap k ℂ) q (α x) = (ρ x).val) ∧
      (∀ x, LaurentPolynomial.eval₂ (algebraMap k ℂ) 1 (α x) = (ρ x).val 0) := by
  let σ := v5EntireTranslation k (2 * Real.pi * Complex.I)
  have hσ (b : LaurentPolynomial k) :
      σ (ρ (algebraMap (LaurentPolynomial k) T b)) =
        ρ (algebraMap (LaurentPolynomial k) T b) := by
    apply Subtype.ext
    funext w
    change (ρ (algebraMap (LaurentPolynomial k) T b)).val
      (w + (2 * Real.pi * Complex.I)) = _
    rw [hbase]
    exact v5KummerEval_period_one b w
  obtain ⟨q, hq, hp⟩ := v5_common_period_of_finite_realization ρ.toRingHom σ.toRingEquiv hσ
  let ρ' : T →ₐ[k] (ℂ → ℂ) := (v5EntireSubalgebra k).val.comp ρ
  have hd (x : T) : Differentiable ℂ (ρ' x) := (ρ x).property
  have hper (x : T) :
      Function.Periodic (ρ' x) ((q : ℂ) * (2 * Real.pi * Complex.I)) := by
    intro w
    have hx := hp x
    change (σ.toRingEquiv ^ q) (ρ x) = ρ x at hx
    rw [← v5AlgEquivRingMonoid_pow] at hx
    have hv := congrArg (fun f : v5EntireSubalgebra k => f.val w) hx
    change (((v5EntireTranslation k (2 * Real.pi * Complex.I) ^ q) (ρ x)).val w) =
      (ρ x).val w at hv
    rw [v5EntireTranslation_pow_apply] at hv
    exact hv
  have hi (x : T) : ∃ p : Polynomial (LaurentPolynomial k),
      p.Monic ∧ p.eval₂ (algebraMap (LaurentPolynomial k) T) x = 0 :=
    IsIntegral.of_finite (LaurentPolynomial k) x
  obtain ⟨α, hα, hmark, _⟩ := v5_marked_kummer_factor ρ'
    (algebraMap (LaurentPolynomial k) T) hbase q hq hd hper hi
  exact ⟨q, hq, α, v5_marked_kummer_factor_base ρ' _ hbase q hq α hα, hα, hmark⟩


/-- A Laurent ring hom is fixed by its coefficients and the image of T. -/
theorem v5_laurent_hom_ext_generator {R D : Type*} [CommRing R] [CommRing D]
    {f g : LaurentPolynomial R →+* D}
    (hC : ∀ a : R, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  open LaurentPolynomial in
  have hneg : f (T (-1)) = g (T (-1)) := by
    apply ((isUnit_T (R := R) (1 : ℤ)).map f).mul_right_inj.mp
    calc
      f (T 1) * f (T (-1)) = 1 := by rw [← map_mul, ← T_add]; norm_num
      _ = f (T 1) * g (T (-1)) := by rw [hT, ← map_mul, ← T_add]; norm_num
  have hp : f.comp (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) =
      g.comp (Polynomial.toLaurent : Polynomial R →+* LaurentPolynomial R) := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, Polynomial.toLaurent_C] using hC a
    · simpa only [RingHom.comp_apply, Polynomial.toLaurent_X] using hT
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on_mul_T with
  | @Qf P n =>
    have hP := congrArg (fun F : Polynomial R →+* D => F P) hp
    have hn : (LaurentPolynomial.T (-(n : ℤ)) : LaurentPolynomial R) =
        LaurentPolynomial.T (-1) ^ n := by
      simp
    rw [map_mul, map_mul, hn, map_pow, map_pow, hneg]
    exact congrArg (· * g (LaurentPolynomial.T (-1)) ^ n) hP

omit [CharZero k] [IsAlgClosed k] in
/-- In the finite-cover theorem, it is enough to check the realization of the
single Laurent variable, provided the realization respects scalar coefficients. -/
theorem v5_kummer_base_of_generator {T : Type*} [CommRing T] [Algebra k T]
    [Algebra (LaurentPolynomial k) T] [IsScalarTower k (LaurentPolynomial k) T]
    (ρ : T →ₐ[k] v5EntireSubalgebra k)
    (hT : (ρ (algebraMap (LaurentPolynomial k) T (LaurentPolynomial.T 1))).val =
      Complex.exp) :
    ∀ b, (ρ (algebraMap (LaurentPolynomial k) T b)).val =
      v5KummerEval (algebraMap k ℂ) 1 b := by
  let ρ' : T →ₐ[k] (ℂ → ℂ) := (v5EntireSubalgebra k).val.comp ρ
  have h : ρ'.toRingHom.comp (algebraMap (LaurentPolynomial k) T) =
      (v5KummerEvalAlg (k := k) 1).toRingHom := by
    apply v5_laurent_hom_ext_generator
    · intro a
      change ρ' (algebraMap (LaurentPolynomial k) T (LaurentPolynomial.C a)) =
        (v5KummerEvalAlg (k := k) 1) (LaurentPolynomial.C a)
      simpa only [LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
        AlgHom.commutes]
    · change (ρ (algebraMap (LaurentPolynomial k) T (LaurentPolynomial.T 1))).val =
        v5KummerEval (algebraMap k ℂ) 1 (LaurentPolynomial.T 1)
      rw [hT]
      funext w
      rw [v5KummerEval_apply, LaurentPolynomial.eval₂_T, zpow_one, v5KummerPoint_val,
        Nat.cast_one, div_one]
  exact fun b => congrArg (fun f : LaurentPolynomial k →+* (ℂ → ℂ) => f b) h

end StrictEUnit
#print axioms StrictEUnit.v5KummerEval_period_one
#print axioms StrictEUnit.v5_finite_marked_kummer_factor
#print axioms StrictEUnit.v5_laurent_hom_ext_generator
#print axioms StrictEUnit.v5_kummer_base_of_generator
