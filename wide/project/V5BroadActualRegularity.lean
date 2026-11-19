import V5BroadActualData
import V5BorelCoefficientField
import V5OrdinarySuperoperatorFamily

noncomputable section
open scoped BigOperators Topology
namespace StrictEUnit

/-- The broad E-function itself admits a polynomial equation over the
algebraic numbers with leading coefficient nonzero away from the origin. -/
theorem v5_actual_broad_annihilator_over_algebraic {f : ℂ → ℂ}
    (hf : V5IsBroadEFunction f) (hf0 : f ≠ 0) :
    ∃ (n : ℕ) (P : ℕ → Polynomial AlgebraicComplex), 0 < n ∧
      (∀ z, v5RowResidual f n P z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (P n).eval₂ (algebraMap AlgebraicComplex ℂ) z ≠ 0 := by
  classical
  obtain ⟨a,hd,hs,⟨m,p,hp,hode⟩,ha⟩ := hf
  let f' : entireFunctionAlgebra := ⟨f,hd⟩
  obtain ⟨hc,hfode⟩ := v5_actual_broad_ode_data f' a hs m p hode
  obtain ⟨F,hmem,q,hF,_,hq,hqode⟩ := v5_broad_factorial_ode_descends a m p hp hfode
  letI : FiniteDimensional ℚ F := hF
  letI : NumberField F := ⟨⟩
  let b := ordinaryBorelFieldCoefficient F a hmem
  let φ : F →+* ℂ := ((algebraicClosure ℚ ℂ).val.comp F.val).toRingHom
  letI : Algebra F ℂ := φ.toAlgebra
  have hne : ∃ n, b n ≠ 0 := by
    by_contra! hz
    apply hf0
    have hf' : f' = 0 := by
      apply entireTaylorAlgHom_injective
      rw [map_zero]
      ext n
      have hc' : φ (b n) = v5FactorialCoeff (entireTaylorAlgHom f') n := hc n
      rw [hz n, map_zero, v5FactorialCoeff] at hc'
      rw [map_zero]
      exact (mul_eq_zero.mp hc'.symm).resolve_left
        (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))
    exact congrArg (fun y : entireFunctionAlgebra => y.val) hf'
  obtain ⟨s,Q,hQ,hrec⟩ :=
    factorialSeries_ode_original_coefficients_recurrence b m q hq hqode
  obtain ⟨t,w,hw,hwode⟩ :=
    polynomial_recurrence_ordinary_series_ode b s Q hQ hrec
  let G : PowerSeries F := PowerSeries.mk b
  obtain ⟨r,hr,c,hcyc⟩ := ordinaryBorel_exists_minimal_cyclic
    (HahnSeries.ofPowerSeries ℤ F G) (ordinaryBorel_laurent_mk_ne_zero b hne)
    (ordinaryBorel_laurent_scalar_relation G t w hw hwode)
  cases r with
  | zero => omega
  | succ n =>
    have hpref := v5_broad_ordinaryDerivativePrefix b
      (v5_broad_arithmetic_descends F a hmem ha) (n+1)
    obtain ⟨u,hu,hval,huode⟩ :=
      v5_broad_borel_local_regularity_of_prefix G n c hcyc hpref
    let B : PowerSeries ℂ := PowerSeries.map φ G
    have hB : ∑ i, ((u i).map (algebraMap F ℂ) : PowerSeries ℂ) *
        (PowerSeries.derivative ℂ)^[i.val] B = 0 := by
      have hmap := congrArg (PowerSeries.map φ) huode
      rw [map_sum, map_zero] at hmap
      change ∑ i, ((u i).map φ : PowerSeries ℂ) *
        (PowerSeries.derivative ℂ)^[i.val] B = 0
      simpa only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe,
        B] using hmap
    have hBF (j : ℕ) : PowerSeries.coeff ℂ j B = v5FactorialCoeff (entireTaylorAlgHom f') j := by
      simpa only [B, G, PowerSeries.coeff_map, PowerSeries.coeff_mk] using (show
        φ (b j) = v5FactorialCoeff (entireTaylorAlgHom f') j from hc j)
    obtain ⟨N,A,hN,hA,hord⟩ :=
      v5_borel_fuchs_ordinary_annihilator_over (Nat.succ_pos n) u hu hval f' B hBF hB
    let P := fun j => (A j).map (algebraMap F AlgebraicComplex)
    have hP (j : ℕ) (z : ℂ) : (P j).eval₂ (algebraMap AlgebraicComplex ℂ) z =
        (A j).eval₂ (algebraMap F ℂ) z := by
      rw [Polynomial.eval₂_map]
      rfl
    refine ⟨N,P,hN,?_, fun z hz => (hP N z).symm ▸ hord z hz⟩
    intro z
    change (∑ j ∈ Finset.range (N+1), (P j).eval₂ (algebraMap AlgebraicComplex ℂ) z *
      iteratedDeriv j f z) = 0
    simpa only [hP] using hA z

/-- In particular the inputs of the affine transfer are now provided by
the actual broad predicate over the same algebraic coefficient field. -/
theorem v5_actual_broad_affine_minimal_row_vanishing {g : ℂ → ℂ}
    (hg : V5IsBroadEFunction g) (hg0 : g ≠ 0)
    (m : ℕ) (a : ℕ → Polynomial AlgebraicComplex) (ha : a m ≠ 0)
    (ha0 : ∀ z, v5RowResidual (fun w => (1-w)*g w) m a z = 0)
    (hmin : ∀ l < m, ¬ v5HasAnnihilatorOrder AlgebraicComplex (fun w => (1-w)*g w) l) :
    ∃ v : Fin m → ℂ → ℂ, v5FiniteGermIndependent 1 v ∧
      ∀ i, AnalyticAt ℂ (v i) 1 ∧ v i 1 = 0 ∧
        ∀ᶠ z in 𝓝 (1 : ℂ), v5RowResidual (v i) m a z = 0 := by
  have hgd : Differentiable ℂ g := by obtain ⟨_,hd,_,_,_⟩ := hg; exact hd
  obtain ⟨n,p,hn,hp,hord⟩ := v5_actual_broad_annihilator_over_algebraic hg hg0
  exact v5_norm_vanishing_family_of_ordinary_superoperator g hgd.analyticAt n m hn p a
    (hord 1 one_ne_zero) ha hp ha0 hmin

#print axioms v5_actual_broad_annihilator_over_algebraic
#print axioms v5_actual_broad_affine_minimal_row_vanishing
end StrictEUnit
end
