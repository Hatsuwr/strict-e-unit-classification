import V5BroadDivisionArithmetic
import V5BroadActualRegularity
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open scoped Topology BigOperators
namespace StrictEUnit

/-- Entire quotient and its literal factorial Taylor coefficients, including
the filled-in value at the removable singularity. -/
theorem v5_entire_division_at_one (f : entireFunctionAlgebra) (hf : f.val 1 = 0)
    (a : ℕ → AlgebraicComplex)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f.val z)) :
    ∃ g : entireFunctionAlgebra, (∀ z, (1-z)*g.val z = f.val z) ∧
      ∀ z : ℂ, HasSum (fun n => ((v5DivisionCoeff a n : AlgebraicComplex) : ℂ) * z ^ n / (n.factorial : ℂ))
        (g.val z) := by
  let G : ℂ → ℂ := fun z => -dslope f.val 1 z
  have hd : Differentiable ℂ G := by
    apply Differentiable.neg
    apply differentiableOn_univ.mp
    exact (Complex.differentiableOn_dslope (s := Set.univ) (c := (1:ℂ)) Filter.univ_mem).mpr
      f.property.differentiableOn
  let g : entireFunctionAlgebra := ⟨G,hd⟩
  have hprod (z : ℂ) : (1-z)*g.val z = f.val z := by
    have h := sub_smul_dslope f.val (1:ℂ) z
    rw [hf, sub_zero, smul_eq_mul] at h
    change (1-z)*(-dslope f.val 1 z) = _
    calc
      _ = (z-1)*dslope f.val 1 z := by ring
      _ = _ := h
  refine ⟨g,hprod,?_⟩
  let b : ℕ → ℂ := fun n => (a n : ℂ)
  let P : Polynomial ℂ := 1-Polynomial.X
  have hfg : polynomialEntireAlgHom P * g = f := by
    apply Subtype.ext
    funext z
    change P.eval z * g.val z = f.val z
    simpa [P] using hprod z
  have hfgT := congrArg entireTaylorAlgHom hfg
  rw [map_mul, entireTaylorAlgHom_polynomial] at hfgT
  have hT : ∀ n : ℕ, PowerSeries.coeff ℂ n (entireTaylorAlgHom f) = b n / (n.factorial : ℂ) := by
    intro n
    rw [entireTaylorAlgHom_apply, coeff_entireFormalTaylor]
    apply entireCauchyCoefficient_eq_of_hasSum f.property
    intro z
    convert hs z using 1
    funext j
    dsimp [b]
    ring
  have hX : (1-PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
    intro h
    have hz := congrArg (PowerSeries.coeff ℂ 0) h
    simp only [map_sub, PowerSeries.coeff_zero_one, PowerSeries.coeff_zero_X, sub_zero,
      map_zero, one_ne_zero] at hz
  have hformal : entireTaylorAlgHom g =
      PowerSeries.mk (fun n => v5DivisionCoeff b n / (n.factorial : ℂ)) := by
    apply mul_left_cancel₀ hX
    rw [v5_factorial_division_formal]
    have hfgT' : (1-PowerSeries.X : PowerSeries ℂ)*entireTaylorAlgHom g =
        entireTaylorAlgHom f := by
      simpa only [P, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_X] using hfgT
    rw [hfgT']
    ext n
    simpa only [PowerSeries.coeff_mk] using hT n
  intro z
  have hsg := entireCauchyCoefficient_hasSum g.property z
  convert hsg using 1
  funext n
  have hcn := congrArg (PowerSeries.coeff ℂ n) hformal
  rw [coeff_entireTaylorAlgHom, PowerSeries.coeff_mk] at hcn
  rw [hcn]
  have hm := v5_divisionCoeff_map (algebraicClosure ℚ ℂ).val.toRingHom a n
  change (algebraicClosure ℚ ℂ).val.toRingHom (v5DivisionCoeff a n) * z^n /
    (n.factorial : ℂ) = _
  rw [hm]
  change v5DivisionCoeff b n * z^n / (n.factorial : ℂ) = _
  ring

/-- Conditional broad division closure: the missing input is the actual
zero of each conjugate at one, not the algebraic division or growth bound. -/
theorem v5_broad_division_at_one (f : ℂ → ℂ) (a : ℕ → AlgebraicComplex)
    (hf : Differentiable ℂ f)
    (hs : ∀ z : ℂ, HasSum (fun n => (a n : ℂ) * z ^ n / (n.factorial : ℂ)) (f z))
    (hODE : HasAlgebraicPolynomialODE f)
    (ha : V5BroadAlgebraicArithmetic a)
    (hz : ∀ σ : AlgebraicComplex →ₐ[ℚ] ℂ,
      HasSum (fun n => σ (a n) / (n.factorial : ℂ)) 0) :
    ∃ g : ℂ → ℂ, V5IsBroadEFunction g ∧ ∀ z, (1-z)*g z = f z := by
  classical
  have hfb : V5IsBroadEFunction f := ⟨a,hf,hs,hODE,ha⟩
  by_cases he : f = 0
  · exact ⟨f,hfb,fun z => by simp [he]⟩
  have hzero : f 1 = 0 := (by simpa only [one_pow, mul_one] using hs 1 :
    HasSum (fun n => (a n : ℂ)/(n.factorial : ℂ)) (f 1)).unique (hz (algebraicClosure ℚ ℂ).val)
  obtain ⟨g,hg,hsg⟩ := v5_entire_division_at_one ⟨f,hf⟩ hzero a hs
  have hgd : Differentiable ℂ g.val := g.property
  obtain ⟨m,p,_,hp,hord⟩ := v5_actual_broad_annihilator_over_algebraic hfb he
  have hp0 : p m ≠ 0 := by
    intro hz
    exact hord 1 one_ne_zero (by rw [hz, Polynomial.eval₂_zero])
  have heq : (fun z => (1-z)*g.val z) = f := funext hg
  have hleft : v5HasAnnihilatorOrder AlgebraicComplex (fun z => (1-z)*g.val z) m :=
    ⟨p,hp0,heq.symm ▸ hp⟩
  obtain ⟨q,hq,hqa⟩ := (v5_affine_hasAnnihilatorOrder_iff hgd.analyticAt m).mp hleft
  have hgo : HasAlgebraicPolynomialODE g.val := by
    refine ⟨m,fun i => q i.val,⟨Fin.last m,hq⟩,?_⟩
    intro z
    rw [Fin.sum_univ_eq_sum_range (fun j => (q j).eval₂
      (algebraicClosure ℚ ℂ).val.toRingHom z * iteratedDeriv j g.val z)]
    exact hqa z
  exact ⟨g.val,⟨v5DivisionCoeff a,hgd,hsg,hgo,v5_broad_algebraic_division_arithmetic a ha hz⟩,hg⟩

#print axioms v5_entire_division_at_one
#print axioms v5_broad_division_at_one
end StrictEUnit
end
