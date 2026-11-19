import V5ActualGaloisScalarRow
import V5ActualMinimalAnalyticFamily
import V5GermVanishingTransfer

noncomputable section
set_option maxHeartbeats 1800000
open scoped BigOperators Topology
namespace StrictEUnit

theorem v5_actual_algebraic_row_residual (f : ℂ → ℂ) (m : ℕ)
    (q : ℕ → Polynomial AlgebraicComplex) :
    v5ActualAlgebraicRow f m (fun i => q i.val) ↔
      ∀ z, v5RowResidual f m q z = 0 := by
  unfold v5ActualAlgebraicRow v5RowResidual
  apply forall_congr'
  intro z
  exact Iff.of_eq (congrArg (fun w : ℂ => w = 0) (Fin.sum_univ_eq_sum_range
    (fun j => (q j).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z * iteratedDeriv j f z) (m+1)))


/-- Each nonzero actual norm factor admits a full analytic family at one
for the corresponding conjugate of the same minimum equation. -/
theorem v5_actual_galois_minimal_analytic_family (K : IntermediateField ℚ AlgebraicComplex)
    (a : ℕ → K) (σ : K ≃ₐ[ℚ] K) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hs : ∀ z, HasSum (fun n => ((a n : AlgebraicComplex) : ℂ)*z^n/(n.factorial : ℂ)) (f z))
    (ho : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic (fun n => (a n : AlgebraicComplex)))
    (m : ℕ) (q : ℕ → Polynomial AlgebraicComplex) (hq : q m ≠ 0)
    (hrow : ∀ z, v5RowResidual f m q z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder AlgebraicComplex f l)
    (hgne : exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ)) ≠ 0) :
    let qσ := fun j => (q j).map (σ.liftNormal AlgebraicComplex).toRingHom
    ∃ u : Fin m → ℂ → ℂ,
      (∀ i, AnalyticAt ℂ (u i) 1) ∧ v5FiniteGermIndependent (1 : ℂ) u ∧
      ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (u i) m qσ z = 0 := by
  let τ := σ.liftNormal AlgebraicComplex
  let g := exponentialGeneratingFunction (fun n => ((σ (a n) : AlgebraicComplex) : ℂ))
  let qσ := fun j => (q j).map τ.toRingHom
  have he (n : ℕ) : τ (a n : AlgebraicComplex) = (σ (a n) : AlgebraicComplex) :=
    σ.liftNormal_commutes AlgebraicComplex (a n)
  have hg : V5IsBroadEFunction g := by
    have h := v5_actual_broad_coefficient_conjugate τ.toAlgHom f
      (fun n => (a n : AlgebraicComplex)) hf hs ho ha
    change V5IsBroadEFunction
      (exponentialGeneratingFunction (fun n => ((τ (a n : AlgebraicComplex)) : ℂ))) at h
    simpa only [he] using h
  have hqσ : qσ m ≠ 0 := (Polynomial.map_ne_zero_iff τ.injective).mpr hq
  have hrowσ : ∀ z, v5RowResidual g m qσ z = 0 := by
    apply (v5_actual_algebraic_row_residual g m qσ).mp
    exact (v5_actual_galois_scalar_row_iff K a σ f hf hs ha m (fun i => q i.val)).mp
      ((v5_actual_algebraic_row_residual f m q).mpr hrow)
  have hminσ (l : ℕ) (hl : l < m) : ¬ v5HasAnnihilatorOrder AlgebraicComplex g l :=
    fun he => hmin l hl ((v5_actual_galois_annihilatorOrder_iff K a σ f hf hs ha l).mpr he)
  exact v5_actual_broad_minimal_analytic_family_at_one g hg hgne m qσ hqσ hrowσ hminσ

/-- All-zero evaluation of one conjugate family's analytic germs forces any
locally analytic solution of any other coefficient embedding to vanish. -/
theorem v5_galois_minimal_family_vanishing_transfer
    {m : ℕ} (hm : 0 < m) (q : ℕ → Polynomial AlgebraicComplex) (hq : q m ≠ 0)
    (τ ρ : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex)
    (u : Fin m → ℂ → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) 1)
    (hind : v5FiniteGermIndependent (1 : ℂ) u)
    (hode : ∀ i, ∀ᶠ z in 𝓝 (1 : ℂ),
      v5RowResidual (u i) m (fun j => (q j).map τ.toRingHom) z = 0)
    (hzero : ∀ i, u i 1 = 0) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g 1)
    (hrow : ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual g m (fun j => (q j).map ρ.toRingHom) z = 0) :
    g 1 = 0 := by
  let ι := (algebraicClosure ℚ ℂ).val.toRingHom
  let φ := ι.comp τ.toRingHom
  let ψ := ι.comp ρ.toRingHom
  have hrel (η : AlgebraicComplex ≃ₐ[ℚ] AlgebraicComplex) (v : ℂ → ℂ) (z : ℂ) :
      v5RowResidual v m (fun j => (q j).map η.toRingHom) z =
        v5RowResidual v m (fun j => (q j).map (ι.comp η.toRingHom)) z := by
    unfold v5RowResidual
    apply Finset.sum_congr rfl
    intro j _
    change ((q j).map η.toRingHom).eval₂ ι z * iteratedDeriv j v z =
      ((q j).map (ι.comp η.toRingHom)).eval z * iteratedDeriv j v z
    rw [Polynomial.eval₂_map,Polynomial.eval_map]
  have hτ := fun i => (hode i).mono (fun z hz => (hrel τ (u i) z).symm.trans hz)
  have hρ := hrow.mono (fun z hz => (hrel ρ g z).symm.trans hz)
  have heφ : φ (1 : AlgebraicComplex) = (1 : ℂ) := map_one φ
  have heψ : ψ (1 : AlgebraicComplex) = (1 : ℂ) := map_one ψ
  have h := v5_analytic_scalar_zero_under_alternate_embedding hm φ ψ q hq 1 u
    (by simpa only [heφ] using hu) (by simpa only [heφ] using hind)
    (by simpa only [heφ,φ] using hτ) (by simpa only [heφ] using hzero) g
    (by simpa only [heψ] using hg) (by simpa only [heψ,ψ] using hρ)
  simpa only [heψ] using h

#print axioms v5_actual_algebraic_row_residual
#print axioms v5_actual_galois_minimal_analytic_family
#print axioms v5_galois_minimal_family_vanishing_transfer
end StrictEUnit
