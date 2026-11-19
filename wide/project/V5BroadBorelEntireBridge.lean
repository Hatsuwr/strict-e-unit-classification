import V5BroadBorelLocalRegularity
import V5BorelSupportAssembly
import OrdinaryBorelMinimalCyclic

noncomputable section
open scoped BigOperators
namespace StrictEUnit

private theorem v5_borel_trailing_map
    {K L : Type*} [Field K] [Field L] (φ : K →+* L) (p : Polynomial K) :
    (p.map φ).natTrailingDegree = p.natTrailingDegree := by
  unfold Polynomial.natTrailingDegree Polynomial.trailingDegree
  rw [Polynomial.support_map_of_injective p φ.injective]

/-- Given a factorial-series equation over the original finite field, pass to
the original ordinary series, use its actual minimal cyclic companion and
transport the resulting Fuchsian equation to the entire function. -/
theorem v5_broad_entire_annihilator_of_prefixes
    {K : Type*} [Field K] [NumberField K] (φ : K →+* ℂ)
    (a : ℕ → K) (ha : ∃ n, a n ≠ 0)
    (f : entireFunctionAlgebra)
    (hcoeff : ∀ n, φ (a n) = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (m : ℕ) (p : Fin (m+1) → Polynomial K) (hp : ∃ i, p i ≠ 0)
    (hode : (∑ i, (p i : PowerSeries K) *
      (PowerSeries.derivative K)^[i.val]
        (PowerSeries.mk (fun n => a n / (n.factorial : K)))) = 0)
    (hprefix : ∀ r, V5BroadIntegralPrefix K (ordinaryDerivativePrefix r (PowerSeries.mk a))) :
    ∃ (n : ℕ) (P : ℕ → Polynomial ℂ), 0 < n ∧
      (∀ z, v5RowResidual f.val n P z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (P n).eval z ≠ 0 := by
  obtain ⟨s, Q, hQ, hrec⟩ :=
    factorialSeries_ode_original_coefficients_recurrence a m p hp hode
  obtain ⟨t, q, hq, hqode⟩ :=
    polynomial_recurrence_ordinary_series_ode a s Q hQ hrec
  let G : PowerSeries K := PowerSeries.mk a
  obtain ⟨r, hr, c, hcyc⟩ := ordinaryBorel_exists_minimal_cyclic
    (HahnSeries.ofPowerSeries ℤ K G)
    (ordinaryBorel_laurent_mk_ne_zero a ha)
    (ordinaryBorel_laurent_scalar_relation G t q hq hqode)
  cases r with
  | zero => omega
  | succ n =>
    obtain ⟨b, hb, hval, hbode⟩ :=
      v5_broad_borel_local_regularity_of_prefix G n c hcyc (hprefix (n+1))
    let B : PowerSeries ℂ := PowerSeries.map φ G
    let bC : Fin (n+1+1) → Polynomial ℂ := fun i => (b i).map φ
    have hlead : bC (Fin.last (n+1)) ≠ 0 := (Polynomial.map_ne_zero_iff φ.injective).2 hb
    have hvalC (i : Fin (n+1+1)) (hi : bC i ≠ 0) :
        (bC (Fin.last (n+1))).natTrailingDegree+i.val ≤ (bC i).natTrailingDegree+(n+1) := by
      simpa only [bC, v5_borel_trailing_map] using
        hval i ((Polynomial.map_ne_zero_iff φ.injective).1 hi)
    have hB : ∑ i, (bC i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] B = 0 := by
      have hmap := congrArg (PowerSeries.map φ) hbode
      rw [map_sum, map_zero] at hmap
      simpa only [map_mul, ordinaryBorel_map_iterate_derivative, ← Polynomial.polynomial_map_coe,
        B, bC] using hmap
    have hBF (j : ℕ) : PowerSeries.coeff ℂ j B = v5FactorialCoeff (entireTaylorAlgHom f) j := by
      simpa only [B, G, PowerSeries.coeff_map, PowerSeries.coeff_mk] using hcoeff j
    exact v5_borel_fuchs_ordinary_annihilator (Nat.succ_pos n) bC hlead hvalC f B hBF hB

#print axioms v5_broad_entire_annihilator_of_prefixes
end StrictEUnit
end
