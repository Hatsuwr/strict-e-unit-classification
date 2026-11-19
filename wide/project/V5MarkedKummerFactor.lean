import V5KummerEvaluation
import V5MonicLaurentAlgebraization

noncomputable section
namespace StrictEUnit

variable {k : Type*} [Field k] [Algebra k ℂ]

def v5KummerEvalAlg (q : ℕ) : LaurentPolynomial k →ₐ[k] (ℂ → ℂ) where
  toRingHom := v5KummerEval (algebraMap k ℂ) q
  commutes' a := by
    funext w
    change v5KummerEval (algebraMap k ℂ) q (LaurentPolynomial.C a) w = algebraMap k ℂ a
    rw [v5KummerEval_apply, LaurentPolynomial.eval₂_C]

theorem v5KummerPoint_pow (q : ℕ) (hq : 0 < q) (w : ℂ) :
    v5KummerPoint q w ^ q = v5KummerPoint 1 w := by
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, v5KummerPoint_val, Nat.cast_one, div_one]
  rw [← Complex.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hqc]

@[simp] theorem v5KummerPoint_zero (q : ℕ) : v5KummerPoint q 0 = 1 := by
  apply Units.ext
  simp

/-- If all realized elements have a common positive period and a monic
relation over the Laurent base, they factor through the marked power cover.
This does not assume that the analytic realization is faithful. -/
theorem v5_marked_kummer_factor {T : Type*} [CommRing T] [Algebra k T]
    [CharZero k] [IsAlgClosed k] (ρ : T →ₐ[k] (ℂ → ℂ))
    (b : LaurentPolynomial k →+* T)
    (hbase : ∀ p, ρ (b p) = v5KummerEval (algebraMap k ℂ) 1 p)
    (q : ℕ) (hq : 0 < q)
    (hd : ∀ x, Differentiable ℂ (ρ x))
    (hper : ∀ x, Function.Periodic (ρ x) ((q : ℂ) * (2 * Real.pi * Complex.I)))
    (hi : ∀ x, ∃ p : Polynomial (LaurentPolynomial k), p.Monic ∧ p.eval₂ b x = 0) :
    ∃ α : T →ₐ[k] LaurentPolynomial k,
      (∀ x, v5KummerEval (algebraMap k ℂ) q (α x) = ρ x) ∧
      (∀ x, LaurentPolynomial.eval₂ (algebraMap k ℂ) 1 (α x) = ρ x 0) ∧
      α (b (LaurentPolynomial.T 1)) = LaurentPolynomial.T (q : ℤ) := by
  let E : LaurentPolynomial k →ₐ[k] (ℂ → ℂ) := v5KummerEvalAlg q
  have hEr (x : T) : ρ x ∈ E.range := by
    obtain ⟨F, hF, hw, _⟩ := v5_periodic_entire_descends _ q hq (hd x) (hper x)
    obtain ⟨p, hp, he⟩ := hi x
    have hrel (t : ℂˣ) :
        (p.map (LaurentPolynomial.eval₂ (algebraMap k ℂ) (t^q))).IsRoot (F t) := by
      obtain ⟨w, rfl⟩ := v5KummerPoint_surjective q hq t
      let ev : T →+* ℂ := (Pi.evalRingHom (fun _ : ℂ => ℂ) w).comp ρ.toRingHom
      have hb : ev.comp b =
          LaurentPolynomial.eval₂ (algebraMap k ℂ) (v5KummerPoint q w ^ q) := by
        apply RingHom.ext
        intro a
        change ρ (b a) w =
          LaurentPolynomial.eval₂ (algebraMap k ℂ) (v5KummerPoint q w ^ q) a
        rw [hbase, v5KummerEval_apply, v5KummerPoint_pow q hq]
      have ht := (v5LaurentSpecialize_relation (algebraMap k ℂ)
        (v5KummerPoint q w) q b ev hb p hp x he).2
      change _ = 0
      rw [show F (v5KummerPoint q w : ℂ) = ev x from hw w]
      exact ht
    obtain ⟨L, hL⟩ := v5_algebraic_laurent_of_monic_laurent_equation
      (algebraMap k ℂ) hp q F (fun z hz => hF.differentiableAt (isOpen_ne.mem_nhds hz)) hrel
    refine ⟨L, ?_⟩
    funext w
    change v5KummerEval (algebraMap k ℂ) q L w = ρ x w
    rw [v5KummerEval_apply, hL]
    exact hw w
  let e := AlgEquiv.ofInjective E (v5KummerEval_injective (algebraMap k ℂ) q hq)
  let α := e.symm.toAlgHom.comp (ρ.codRestrict E.range hEr)
  have hα (x : T) : v5KummerEval (algebraMap k ℂ) q (α x) = ρ x := by
    change (e (e.symm (ρ.codRestrict E.range hEr x)) : ℂ → ℂ) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨α, hα, fun x => ?_, ?_⟩
  · have he := congrFun (hα x) 0
    rwa [v5KummerEval_apply, v5KummerPoint_zero] at he
  · apply v5KummerEval_injective (algebraMap k ℂ) q hq
    rw [hα, hbase]
    funext w
    rw [v5KummerEval_apply, v5KummerEval_apply, LaurentPolynomial.eval₂_T_n]
    change LaurentPolynomial.eval₂ (algebraMap k ℂ) (v5KummerPoint 1 w)
      (LaurentPolynomial.T (1 : ℤ)) = ((v5KummerPoint q w ^ q : ℂˣ) : ℂ)
    rw [v5KummerPoint_pow q hq, LaurentPolynomial.eval₂_T, zpow_one]


/-- Substitution of the qth power of the Laurent variable. -/
def v5LaurentPower {k : Type*} [CommRing k] (q : ℕ) :
    LaurentPolynomial k →+* LaurentPolynomial k :=
  LaurentPolynomial.eval₂ LaurentPolynomial.C
    ⟨LaurentPolynomial.T (q : ℤ), LaurentPolynomial.T (-(q : ℤ)),
      by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
      by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩

theorem v5LaurentPower_eval (ι : k →+* ℂ) (q : ℕ) (t : ℂˣ) (p : LaurentPolynomial k) :
    LaurentPolynomial.eval₂ ι t (v5LaurentPower q p) =
      LaurentPolynomial.eval₂ ι (t ^ q) p := by
  let u : (LaurentPolynomial k)ˣ :=
    ⟨LaurentPolynomial.T (q : ℤ), LaurentPolynomial.T (-(q : ℤ)),
      by rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero],
      by rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]⟩
  let ev := LaurentPolynomial.eval₂ ι t
  have hu : Units.map ev.toMonoidHom u = t ^ q := by
    apply Units.ext
    change ev (LaurentPolynomial.T (q : ℤ)) = _
    rw [LaurentPolynomial.eval₂_T_n]
    rfl
  change ev (LaurentPolynomial.eval₂ LaurentPolynomial.C u p) = _
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T]
    rw [show ev (LaurentPolynomial.C a) = ι a from LaurentPolynomial.eval₂_C _ _ _]
    rw [show ev ((u ^ n : (LaurentPolynomial k)ˣ) : LaurentPolynomial k) =
      ((Units.map ev.toMonoidHom (u ^ n) : ℂˣ) : ℂ) from rfl, map_zpow, hu]

/-- The comparison respects the whole Laurent base, not just its generator. -/
theorem v5_marked_kummer_factor_base {T : Type*} [CommRing T] [Algebra k T]
    (ρ : T →ₐ[k] (ℂ → ℂ)) (b : LaurentPolynomial k →+* T)
    (hbase : ∀ p, ρ (b p) = v5KummerEval (algebraMap k ℂ) 1 p)
    (q : ℕ) (hq : 0 < q) (α : T →ₐ[k] LaurentPolynomial k)
    (hα : ∀ x, v5KummerEval (algebraMap k ℂ) q (α x) = ρ x) :
    α.toRingHom.comp b = v5LaurentPower q := by
  apply RingHom.ext
  intro p
  apply v5KummerEval_injective (algebraMap k ℂ) q hq
  change v5KummerEval (algebraMap k ℂ) q (α (b p)) = _
  rw [hα, hbase]
  funext w
  rw [v5KummerEval_apply, v5KummerEval_apply, v5LaurentPower_eval, v5KummerPoint_pow q hq]

end StrictEUnit
#print axioms StrictEUnit.v5KummerEvalAlg
#print axioms StrictEUnit.v5KummerPoint_pow
#print axioms StrictEUnit.v5_marked_kummer_factor
#print axioms StrictEUnit.v5LaurentPower_eval
#print axioms StrictEUnit.v5_marked_kummer_factor_base
