import V5BroadActualProduct
import GaloisPowerSeriesProduct
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

noncomputable section
set_option maxHeartbeats 750000
set_option synthInstance.maxHeartbeats 35000
open scoped BigOperators
namespace StrictEUnit

theorem v5_broad_actual_nonempty_product {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, V5IsBroadEFunction (f i)) :
    V5IsBroadEFunction (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert i s hi ih =>
    by_cases hn : s.Nonempty
    · simpa only [Finset.prod_insert hi] using
        v5_broad_actual_mul (h i (Finset.mem_insert_self i s))
          (ih hn (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn] at h ⊢
      simpa using h i (Finset.mem_insert_self i ∅)

/-- The actual Galois norm is a product of separately realized conjugate
series. No map has been applied to any complex function value. -/
def v5BroadGaloisNorm (K : IntermediateField ℚ AlgebraicComplex)
    [Fintype (K ≃ₐ[ℚ] K)] (a : ℕ → K) : ℂ → ℂ :=
  fun z => ∏ σ : K ≃ₐ[ℚ] K,
    exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ)) z

/-- The same finite coefficient norm is a genuine broad E-function, with
rational factorial coefficients. It inherits the distinguished zero and
cannot vanish identically unless the original function does. The number
field is supplied with its finite Galois structures. -/
theorem v5_broad_galois_norm_properties (K : IntermediateField ℚ AlgebraicComplex)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [Fintype (K ≃ₐ[ℚ] K)]
    (a : ℕ → K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex))) :
    (∃ b : ℕ → AlgebraicComplex, Differentiable ℂ (v5BroadGaloisNorm K a) ∧
      (∀ z, HasSum (fun n => (b n : ℂ)*z^n/(n.factorial : ℂ)) (v5BroadGaloisNorm K a z)) ∧
      HasAlgebraicPolynomialODE (v5BroadGaloisNorm K a) ∧ V5BroadAlgebraicArithmetic b ∧
      (∀ n, ∃ q : ℚ, b n = algebraMap ℚ AlgebraicComplex q)) ∧
    (f ≠ 0 → v5BroadGaloisNorm K a ≠ 0) ∧
    (f 1 = 0 → v5BroadGaloisNorm K a 1 = 0) := by
  classical
  let k := (algebraicClosure ℚ ℂ).toSubfield
  let c : (K ≃ₐ[ℚ] K) → ℕ → AlgebraicComplex := fun σ n => (σ (a n) : AlgebraicComplex)
  let g : (K ≃ₐ[ℚ] K) → ℂ → ℂ :=
    fun σ => exponentialGeneratingFunction (fun n => (c σ n : ℂ))
  have he (σ : K ≃ₐ[ℚ] K) :
      (fun n => (σ.toAlgHom.liftNormal AlgebraicComplex) (a n : AlgebraicComplex)) = c σ := by
    funext n
    exact σ.toAlgHom.liftNormal_commutes AlgebraicComplex (a n)
  have hca (σ : K ≃ₐ[ℚ] K) : V5BroadAlgebraicArithmetic (c σ) := by
    rw [← he σ]
    exact v5_broad_algebraic_arithmetic_map (σ.toAlgHom.liftNormal AlgebraicComplex) _ ha
  have hg (σ : K ≃ₐ[ℚ] K) : V5IsBroadEFunction (g σ) := by
    have h := v5_actual_broad_coefficient_conjugate (σ.toAlgHom.liftNormal AlgebraicComplex)
      f (fun n => (a n : AlgebraicComplex)) hf hs hODE ha
    change V5IsBroadEFunction (exponentialGeneratingFunction
      (fun n => ((fun j => (σ.toAlgHom.liftNormal AlgebraicComplex) (a j : AlgebraicComplex)) n : ℂ))) at h
    rw [he σ] at h
    exact h
  let F : (K ≃ₐ[ℚ] K) → subfieldEntireFunctionAlgebra k := fun σ =>
    v5FactorialEntire (g σ) (v5_broad_series_hasSum_entire (c σ) (hca σ)).1 (c σ)
      (v5_broad_series_hasSum_entire (c σ) (hca σ)).2
  let G : subfieldEntireFunctionAlgebra k := ∏ σ, F σ
  let x : PowerSeries K := PowerSeries.mk (fun n => a n / (n.factorial : K))
  let P : PowerSeries K := ∏ σ : K ≃ₐ[ℚ] K, PowerSeries.map σ.toRingHom x
  have hG (z : ℂ) : G.val.val z = v5BroadGaloisNorm K a z := by
    change stage14_subfieldEntireEvaluation k z (∏ σ, F σ) =
      ∏ σ, stage14_subfieldEntireEvaluation k z (F σ)
    exact map_prod _ _ _
  have hT : subfieldEntireTaylorAlgHom k G = PowerSeries.map K.val.toRingHom P := by
    dsimp only [G,P]
    rw [map_prod,map_prod]
    apply Finset.prod_congr rfl
    intro σ _
    change subfieldEntireTaylorAlgHom k
      (v5FactorialEntire (g σ) _ (c σ) _) = _
    rw [v5_factorialEntire_taylor]
    simp only [x, v5_factorial_series_map]
    rfl
  have hnorm : V5IsBroadEFunction (v5BroadGaloisNorm K a) :=
    v5_broad_actual_nonempty_product Finset.univ ⟨1, Finset.mem_univ _⟩ g (fun σ _ => hg σ)
  obtain ⟨b,hdb,hsb,hob,hab⟩ := hnorm
  have hG' : G.val.val = v5BroadGaloisNorm K a := funext hG
  refine ⟨⟨b,hdb,hsb,hob,hab,?_⟩,?_,?_⟩
  · intro n
    have hrat : ∃ q : ℚ, algebraMap ℚ K q = PowerSeries.coeff K n P := by
      apply powerSeries_prod_coeff_rational_of_permuted
        (fun σ : K ≃ₐ[ℚ] K => PowerSeries.map σ.toRingHom x) _ n
      intro τ
      refine ⟨Equiv.mulLeft τ,?_⟩
      intro σ
      ext j
      simp only [PowerSeries.coeff_map]
      rfl
    obtain ⟨q,hq⟩ := hrat
    refine ⟨q*(n.factorial : ℚ),?_⟩
    have he : PowerSeries.coeff AlgebraicComplex n (subfieldEntireTaylorAlgHom k G) =
        algebraMap ℚ AlgebraicComplex q := by
      rw [hT,PowerSeries.coeff_map,← hq]
      exact K.val.commutes q
    have hc := congrArg (algebraicClosure ℚ ℂ).val he
    have hcn : entireCauchyCoefficient G.val.val n = (q : ℂ) := by
      simpa only [subfieldEntireTaylorAlgHom_apply,subfieldEntireTaylorSeries,
        PowerSeries.coeff_mk,AlgHom.commutes] using hc
    rw [hG',v5_factorial_series_cauchyCoefficient _ hdb b hsb] at hcn
    apply (algebraicClosure ℚ ℂ).val.injective
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
    simpa only [AlgHom.commutes,map_mul,Rat.cast_natCast] using (div_eq_iff hn).mp hcn
  · intro hfne hn
    have hx : x ≠ 0 := by
      intro hz
      have ha0 (n : ℕ) : a n = 0 := by
        have hc := congrArg (PowerSeries.coeff K n) hz
        simp only [x,PowerSeries.coeff_mk,map_zero] at hc
        exact (div_eq_zero_iff.mp hc).resolve_right (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
      apply hfne
      funext z
      have he : HasSum (fun _ : ℕ => (0 : ℂ)) (f z) := by simpa [ha0] using hs z
      exact he.unique hasSum_zero
    have hP : P ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro σ _
      intro he
      apply hx
      apply PowerSeries.map_injective σ.toRingHom σ.injective
      simpa only [map_zero] using he
    have hz : G = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hG'.trans hn
    apply hP
    apply PowerSeries.map_injective K.val.toRingHom K.val.injective
    rw [map_zero,← hT,hz,map_zero]
  · intro hzero
    apply Finset.prod_eq_zero (Finset.mem_univ (1 : K ≃ₐ[ℚ] K))
    change g 1 1 = 0
    have h1 := (v5_broad_series_hasSum_entire (c 1) (hca 1)).2 1
    exact (h1.unique (hs 1)).trans hzero

/-- Choose a finite Galois field from the actual broad function and apply
the literal norm-product theorem; this leaves no abstract field hypothesis. -/
theorem v5_broad_exists_rational_galois_norm {f : ℂ → ℂ} (hf : V5IsBroadEFunction f) :
    ∃ g : ℂ → ℂ, (∃ b : ℕ → AlgebraicComplex, Differentiable ℂ g ∧
      (∀ z, HasSum (fun n => (b n : ℂ)*z^n/(n.factorial : ℂ)) (g z)) ∧
      HasAlgebraicPolynomialODE g ∧ V5BroadAlgebraicArithmetic b ∧
      (∀ n, ∃ q : ℚ, b n = algebraMap ℚ AlgebraicComplex q)) ∧
      (f ≠ 0 → g ≠ 0) ∧ (f 1 = 0 → g 1 = 0) := by
  obtain ⟨a,hd,hs,⟨m,p,hp,ho⟩,ha⟩ := hf
  have hformal := (v5_actual_broad_ode_data ⟨f,hd⟩ a hs m p ho).2
  obtain ⟨E,hmem,_,hE,_,_,_⟩ := v5_broad_factorial_ode_descends a m p hp hformal
  letI : FiniteDimensional ℚ E := hE
  let K : IntermediateField ℚ AlgebraicComplex :=
    IntermediateField.normalClosure ℚ E AlgebraicComplex
  letI : FiniteDimensional ℚ K := inferInstance
  letI : IsGalois ℚ K := inferInstance
  letI : Fintype (K ≃ₐ[ℚ] K) := AlgEquiv.fintype ℚ K
  let aK : ℕ → K := fun n => ⟨a n, IntermediateField.le_normalClosure E (hmem n)⟩
  exact ⟨v5BroadGaloisNorm K aK,
    v5_broad_galois_norm_properties K aK f hd hs ⟨m,p,hp,ho⟩ ha⟩

#print axioms v5_broad_exists_rational_galois_norm
#print axioms v5_broad_actual_nonempty_product
#print axioms v5_broad_galois_norm_properties
end StrictEUnit
end
