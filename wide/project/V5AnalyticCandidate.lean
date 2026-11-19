import V5TaylorMatrixODE
import V5FormalMatrixUniqueness
import V5AdjoinRealization
import V5WidePointedCandidate
import V5WidePointedFieldCandidate

noncomputable section
open scoped Matrix.L2OpNorm Topology
namespace StrictEUnit

def v5EntireExpUnit : entireFunctionAlgebraˣ where
  val := ⟨Complex.exp, Complex.differentiable_exp⟩
  inv := ⟨fun w => Complex.exp (-w), Complex.differentiable_exp.comp differentiable_neg⟩
  val_inv := by ext w; change Complex.exp w * Complex.exp (-w) = 1
                rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  inv_val := by ext w; change Complex.exp (-w) * Complex.exp w = 1
                rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

def v5EntireLaurentEval {K : Type*} [Field K] (f : K →+* ℂ) :
    LaurentPolynomial K →+* entireFunctionAlgebra :=
  LaurentPolynomial.eval₂ ((algebraMap ℂ entireFunctionAlgebra).comp f) v5EntireExpUnit

theorem v5EntireLaurentEval_apply {K : Type*} [Field K] (f : K →+* ℂ)
    (p : LaurentPolynomial K) (w : ℂ) :
    (v5EntireLaurentEval f p).val w =
      LaurentPolynomial.eval₂ f (Units.mk0 _ (Complex.exp_ne_zero w)) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb =>
    rw [(v5EntireLaurentEval f).map_add, map_add]
    exact congrArg₂ (· + ·) ha hb
  | C_mul_T n a =>
    simp only [v5EntireLaurentEval, LaurentPolynomial.eval₂_C_mul_T]
    change f a * (v5EntireExpUnit ^ n).val.val w = _
    let ev : entireFunctionAlgebra →* ℂ :=
      { toFun := fun g => g.val w, map_one' := rfl, map_mul' := fun _ _ => rfl }
    change f a * (Units.map ev (v5EntireExpUnit ^ n)).val = _
    rw [map_zpow]
    have he : Units.map ev v5EntireExpUnit = Units.mk0 _ (Complex.exp_ne_zero w) := Units.ext rfl
    rw [he]

theorem v5EntireLaurentEval_log_taylor {K : Type*} [Field K] (f : K →+* ℂ)
    (p : LaurentPolynomial K) :
    v5EntireLogTaylorAlgHom (v5EntireLaurentEval f p) =
      PowerSeries.map f (v5WidePointedBase K p) := by
  let g := v5EntireLogPullback (v5EntireLaurentEval f p)
  let b := v5LocalLaurentEval f p
  have h : g.val =ᶠ[𝓝 (1 : ℂ)] b.val := by
    filter_upwards [isOpen_ne.mem_nhds (one_ne_zero : (1 : ℂ) ≠ 0)] with z hz
    change (v5EntireLaurentEval f p).val (Complex.log z) = b.val z
    rw [v5EntireLaurentEval_apply, v5LocalLaurentEval_apply f p z hz]
    have he : Units.mk0 _ (Complex.exp_ne_zero (Complex.log z)) = Units.mk0 z hz :=
      Units.ext (Complex.exp_log hz)
    rw [he]
  change v5LocalTaylor g.val 1 = _
  rw [(v5LocalTaylor_eq_iff_eventuallyEq g.property b.property).mpr h]
  exact v5LocalLaurentEval_taylor f p

/-- Entire normalized frame on the logarithmic cover, with Taylor comparison to
the actual formal frame and its inverse determinant. -/
theorem v5_entire_formal_frame_comparison {K : Type*} [Field K] [CharZero K]
    (f : K →+* ℂ) {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    ∃ (U : Matrix (Fin r) (Fin r) entireFunctionAlgebra) (v : entireFunctionAlgebra),
      v * U.det = 1 ∧
      U.map v5EntireLogTaylorAlgHom = (v5WidePointedFundamental A).map (PowerSeries.map f) ∧
      v5EntireLogTaylorAlgHom v = PowerSeries.map f ((v5WidePointedFundamental A).det⁻¹) := by
  obtain ⟨U, v, hU, hv, huv, h0, hode⟩ := v5_laurent_matrix_ode_taylor f A
  let M : Matrix (Fin r) (Fin r) entireFunctionAlgebra :=
    fun i j => ⟨fun w => U w i j, v5_matrix_entry_differentiable hU i j⟩
  let v' : entireFunctionAlgebra := ⟨v, hv⟩
  have hmul : v' * M.det = 1 := by
    apply Subtype.ext
    funext w
    let ev : entireFunctionAlgebra →+* ℂ :=
      { toFun := fun p => p.val w, map_one' := rfl, map_zero' := rfl,
        map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl }
    change ev (v' * M.det) = ev 1
    rw [map_mul, RingHom.map_det, map_one]
    exact huv w
  have hmap : M.map v5EntireLogTaylorAlgHom =
      (v5WidePointedFundamental A).map (PowerSeries.map f) := by
    change Matrix.of (fun i j => v5LocalTaylor (fun z => U (Complex.log z) i j) 1) = _
    rw [v5WidePointedFundamental, v5_formalFundamentalMatrix_map]
    exact v5_eq_formalFundamentalMatrix _ _ hode h0
  refine ⟨M, v', hmul, hmap, ?_⟩
  have h1 := congrArg v5EntireLogTaylorAlgHom hmul
  rw [map_mul, AlgHom.map_det, map_one] at h1
  change v5EntireLogTaylorAlgHom v' * (M.map v5EntireLogTaylorAlgHom).det = 1 at h1
  rw [hmap] at h1
  change v5EntireLogTaylorAlgHom v' *
    ((PowerSeries.map f).mapMatrix (v5WidePointedFundamental A)).det = 1 at h1
  rw [← RingHom.map_det] at h1
  have h2 : PowerSeries.map f ((v5WidePointedFundamental A).det⁻¹) *
      PowerSeries.map f (v5WidePointedFundamental A).det = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel _ (by rw [v5WidePointedFundamental_det_constant]; exact one_ne_zero), map_one]
  exact left_inv_eq_right_inv h1 (by rw [mul_comm]; exact h2)


/-- The actual pointed candidate embeds in entire functions on the logarithmic
cover, preserving the exact normalized formal germ. -/
theorem v5_pointed_candidate_entire_realization {K : Type*} [Field K] [CharZero K]
    (f : K →+* ℂ) {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    ∃ ρ : v5WidePointedCandidate A →+* entireFunctionAlgebra,
      Function.Injective ρ ∧
      (∀ x, v5EntireLogTaylorAlgHom (ρ x) = PowerSeries.map f x.val) ∧
      (∀ p, ρ (v5WidePointedCandidateBase A p) = v5EntireLaurentEval f p) := by
  letI : Algebra K (PowerSeries ℂ) :=
    ((PowerSeries.C ℂ).comp f).toAlgebra
  letI : Algebra K entireFunctionAlgebra :=
    ((algebraMap ℂ entireFunctionAlgebra).comp f).toAlgebra
  let i : PowerSeries K →ₐ[K] PowerSeries ℂ :=
    { PowerSeries.map f with
      commutes' := by
        intro a
        change PowerSeries.map f (PowerSeries.C K a) = PowerSeries.C ℂ (f a)
        exact PowerSeries.map_C _ _ }
  let j : entireFunctionAlgebra →ₐ[K] PowerSeries ℂ :=
    { v5EntireLogTaylorAlgHom.toRingHom with
      commutes' := fun a => v5EntireLogTaylorAlgHom.commutes (f a) }
  have hj : Function.Injective j := v5EntireLogTaylorAlgHom_injective
  obtain ⟨U, v, _, hU, hv⟩ := v5_entire_formal_frame_comparison f A
  let s : Set (PowerSeries K) := Set.range (v5WidePointedBase K) ∪
    Set.range (fun ij : Fin r × Fin r => v5WidePointedFundamental A ij.1 ij.2) ∪
    {(v5WidePointedFundamental A).det⁻¹}
  have hs : ∀ x ∈ s, ∃ a, j a = i x := by
    intro x hx
    rcases hx with (⟨p, rfl⟩ | ⟨⟨u,w⟩, rfl⟩) | hx
    · exact ⟨_, v5EntireLaurentEval_log_taylor f p⟩
    · exact ⟨U u w, congrArg (fun M => M u w) hU⟩
    · have he : x = (v5WidePointedFundamental A).det⁻¹ := hx
      rw [he]
      exact ⟨v, hv⟩
  obtain ⟨ρ, hρ, hinj⟩ := v5_adjoin_realization i j hj s hs
  have ht (x : v5WidePointedCandidate A) :
      v5EntireLogTaylorAlgHom (ρ x) = PowerSeries.map f x.val :=
    DFunLike.congr_fun hρ x
  refine ⟨ρ.toRingHom, hinj (PowerSeries.map_injective f f.injective), ht, ?_⟩
  intro p
  apply v5EntireLogTaylorAlgHom_injective
  rw [v5EntireLaurentEval_log_taylor]
  exact ht (v5WidePointedCandidateBase A p)


/-- Transfer the entire realization to the actual Laurent-series candidate.
This preserves both the exponential base and the marked point. -/
theorem v5_field_candidate_entire_realization {K : Type*} [Field K] [CharZero K]
    (f : K →+* ℂ) {r : ℕ} (A : Matrix (Fin r) (Fin r) (LaurentPolynomial K)) :
    ∃ ρ : V5WideFieldCandidate A →+* entireFunctionAlgebra,
      Function.Injective ρ ∧
      (∀ p, ρ (algebraMap (LaurentPolynomial K) (V5WideFieldCandidate A) p) =
        v5EntireLaurentEval f p) ∧
      (∀ x, (ρ x).val 0 = f (v5WideFieldCandidatePoint A x)) := by
  obtain ⟨σ, hinj, ht, hb⟩ := v5_pointed_candidate_entire_realization f A
  let e := (v5WidePointedFieldEquiv A).symm
  refine ⟨σ.comp e.toRingEquiv.toRingHom, hinj.comp e.injective, ?_, ?_⟩
  · intro p
    change σ (e (v5WidePointedFieldEquiv A (v5WidePointedCandidateBase A p))) = _
    rw [(v5WidePointedFieldEquiv A).symm_apply_apply, hb]
  · intro x
    have h := congrArg (PowerSeries.constantCoeff ℂ) (ht (e x))
    change PowerSeries.constantCoeff ℂ
      (v5LocalTaylor (fun z => (σ (e x)).val (Complex.log z)) 1) = _ at h
    rw [v5LocalTaylor_constantCoeff, Complex.log_one,
      ← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff] at h
    exact h

end StrictEUnit
#print axioms StrictEUnit.v5EntireLaurentEval_apply
#print axioms StrictEUnit.v5EntireLaurentEval_log_taylor
#print axioms StrictEUnit.v5_entire_formal_frame_comparison
#print axioms StrictEUnit.v5_pointed_candidate_entire_realization
#print axioms StrictEUnit.v5_field_candidate_entire_realization
