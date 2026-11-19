import V5ActualGaloisGermFamily

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators Topology
namespace StrictEUnit

/-- Every algebraic embedding into the complex numbers has values in the
literal algebraic closure. This uses integrality, not continuity. -/
def v5AlgebraicEmbeddingCorestrict (ψ : AlgebraicComplex →ₐ[ℚ] ℂ) :
    AlgebraicComplex →ₐ[ℚ] AlgebraicComplex :=
  ψ.codRestrict (algebraicClosure ℚ ℂ).toSubalgebra
    (fun x => (Algebra.IsIntegral.isIntegral x).map ψ)

/-- Actual scalar equations map to the independently realized conjugate
series. The conclusion keeps the exact polynomial tuple. -/
theorem v5_actual_scalar_row_map
    (σ : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex)
    (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ha : V5BroadAlgebraicArithmetic a)
    (m : ℕ) (q : ℕ → Polynomial AlgebraicComplex)
    (hr : ∀ z, v5RowResidual f m q z = 0) :
    ∀ z, v5RowResidual (exponentialGeneratingFunction (fun n => (σ (a n) : ℂ)))
      m (fun j => (q j).map σ.toRingHom) z = 0 := by
  obtain ⟨hd,hg⟩ := v5_broad_series_hasSum_entire _ (v5_broad_algebraic_arithmetic_map σ a ha)
  apply (v5_actual_algebraic_row_residual _ m _).mp
  apply (v5_actual_algebraic_row_iff_factorial _ hd _ hg m _).mpr
  have hformal := (v5_actual_algebraic_row_iff_factorial f hf a hs m (fun i => q i.val)).mp
    ((v5_actual_algebraic_row_residual f m q).mpr hr)
  have he := congrArg (PowerSeries.map σ.toRingHom) hformal
  rw [map_sum,map_zero] at he
  simpa only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe,
    v5FactorialSeries,v5_factorial_series_map] using he

/-- A zero evaluation functional on one conjugate's full local solution
family forces every embedding of the original factorial coefficients to
sum to zero at one. -/
theorem v5_actual_wide_embedding_vanishing
    (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => (a n : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ha : V5BroadAlgebraicArithmetic a)
    (m : ℕ) (hm : 0 < m) (q : ℕ → Polynomial AlgebraicComplex) (hq : q m ≠ 0)
    (hr : ∀ z, v5RowResidual f m q z = 0)
    (τ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (u : Fin m → ℂ → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) 1)
    (hind : v5FiniteGermIndependent (1 : ℂ) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ),
      v5RowResidual (u i) m (fun j => (q j).map τ.toRingHom) z = 0)
    (hzero : ∀ i, u i 1 = 0) :
    ∀ ψ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => ψ (a n) / (n.factorial : ℂ)) 0 := by
  intro ψ
  let σ := v5AlgebraicEmbeddingCorestrict ψ
  let g := exponentialGeneratingFunction (fun n => (σ (a n) : ℂ))
  let ι := (algebraicClosure ℚ ℂ).val.toRingHom
  let φ := ι.comp τ.toRingHom
  obtain ⟨hd,hg⟩ := v5_broad_series_hasSum_entire _ (v5_broad_algebraic_arithmetic_map σ a ha)
  have hrow := v5_actual_scalar_row_map σ f a hf hs ha m q hr
  have hrel (η : AlgebraicComplex →ₐ[ℚ] AlgebraicComplex) (v : ℂ → ℂ) (z : ℂ) :
      v5RowResidual v m (fun j => (q j).map η.toRingHom) z =
        v5RowResidual v m (fun j => (q j).map (ι.comp η.toRingHom)) z := by
    unfold v5RowResidual
    apply Finset.sum_congr rfl
    intro j _
    change ((q j).map η.toRingHom).eval₂ ι z * iteratedDeriv j v z =
      ((q j).map (ι.comp η.toRingHom)).eval z * iteratedDeriv j v z
    rw [Polynomial.eval₂_map,Polynomial.eval_map]
  have hτ := fun i => (hode i).mono (fun z hz => (hrel τ.toAlgHom (u i) z).symm.trans hz)
  have hσ : ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual g m (fun j => (q j).map ψ.toRingHom) z = 0 := by
    apply Filter.Eventually.of_forall
    intro z
    exact (hrel σ g z).symm.trans (hrow z)
  have heφ : φ (1 : AlgebraicComplex) = (1 : ℂ) := map_one φ
  have heψ : ψ.toRingHom (1 : AlgebraicComplex) = (1 : ℂ) := map_one ψ
  have hz := v5_analytic_scalar_zero_under_alternate_embedding hm φ ψ.toRingHom q hq 1 u
    (by simpa only [heφ] using hu) (by simpa only [heφ] using hind)
    (by simpa only [heφ,φ] using hτ) (by simpa only [heφ] using hzero) g
    (by simpa only [heψ] using hd.analyticAt 1) (by simpa only [heψ] using hσ)
  have hz' : g 1 = 0 := by simpa only [heψ] using hz
  have hsum := hg 1
  change HasSum (fun n => ψ (a n)*1^n/(n.factorial : ℂ)) (g 1) at hsum
  simpa only [one_pow,mul_one,hz'] using hsum

#print axioms v5AlgebraicEmbeddingCorestrict
#print axioms v5_actual_scalar_row_map
#print axioms v5_actual_wide_embedding_vanishing
end StrictEUnit
