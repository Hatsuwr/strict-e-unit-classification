import LogSolutionConnectionIntertwining
import LaurentPrefixProductArithmetic

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- Natural prefix arithmetic transports to every integer Laurent index,
including the automatically zero negative coefficients. -/
theorem logFilter_powerSeries_prefix_integral (f : PowerSeries K) (D : K) (N : ℕ)
    (hf : ∀ n,n≤N →IsIntegral ℤ (D*PowerSeries.coeff K n f)) :
    ∀ k : ℤ,k≤(N : ℤ) →IsIntegral ℤ (D*(HahnSeries.ofPowerSeries ℤ K f).coeff k) := by
  intro k hk
  by_cases hkn : k<0
  · rw [powerSeries_laurent_coeff_neg f k hkn,mul_zero]
    exact isIntegral_zero
  · obtain ⟨n,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0≤k)
    rw [HahnSeries.ofPowerSeries_apply_coeff]
    exact hf n (by exact_mod_cast hk)

/-- Once the connection matrix vanishes up to N+L-W, its coefficient at N+L
uses only the fixed source jet up to W. It does NOT require arithmetic for
all preceding solution coefficients. -/
theorem logFilter_matrix_product_finite_jet_integral {r : ℕ}
    (F : Matrix (Fin r) (Fin r) (PowerSeries K))
    (Y : Fin r → Polynomial (LaurentSeries K)) (N : ℕ) (L W : ℤ) (D e : K)
    (hFlow : ∀ i j k,k<(N : ℤ)+L-W →(HahnSeries.ofPowerSeries ℤ K (F i j)).coeff k=0)
    (hYlow : ∀ j t k,k<L →((Y j).coeff t).coeff k=0)
    (hFden : ∀ i j k,k≤N →IsIntegral ℤ (D*PowerSeries.coeff K k (F i j)))
    (hYjet : ∀ j t k,k≤W →IsIntegral ℤ (e*((Y j).coeff t).coeff k))
    (i : Fin r) (t : ℕ) :
    IsIntegral ℤ (D*e*((∑ j,logPowerSeriesEmbedding (F i j)*Y j).coeff t).coeff ((N : ℤ)+L)) := by
  change IsIntegral ℤ (D*e*((∑ j,Polynomial.C (HahnSeries.ofPowerSeries ℤ K (F i j))*Y j).coeff t).coeff ((N : ℤ)+L))
  simp only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul,HahnSeries.coeff_sum,Finset.mul_sum]
  apply IsIntegral.sum
  intro j hj
  apply forcing_laurent_product_integral _ _ ((N : ℤ)+L-W) L ((N : ℤ)+L) D e
    (hFlow i j) (hYlow j t) ?_ ?_ _ le_rfl
  · intro k hk
    apply logFilter_powerSeries_prefix_integral (F i j) D N (hFden i j) k
    omega
  · intro k hk
    exact hYjet j t k (by omega)

/-- Arithmetic of a filtered ACTUAL solution follows from connection bounds
and a fixed finite initial jet once high connection vanishing is established.
No arithmetic of the filtered solution is supplied as a premise. -/
theorem literalLogPolynomialFilter_finite_jet_integral {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (rho : K)
    (Y : Fin r → Polynomial (LaurentSeries K))
    (hY : ∀ i,twistedLogPolynomialEuler rho (Y i)=∑ j,logPowerSeriesEmbedding (C i j)*Y j)
    (P : Polynomial K) (N : ℕ) (L W : ℤ) (D e : K)
    (hFlow : ∀ i j k,k<(N : ℤ)+L-W →
      (HahnSeries.ofPowerSeries ℤ K (powerSeriesEulerPolynomialConnection C P i j)).coeff k=0)
    (hYlow : ∀ j t k,k<L →((Y j).coeff t).coeff k=0)
    (hFden : ∀ i j k,k≤N →IsIntegral ℤ (D*PowerSeries.coeff K k
      (powerSeriesEulerPolynomialConnection C P i j)))
    (hYjet : ∀ j t k,k≤W →IsIntegral ℤ (e*((Y j).coeff t).coeff k))
    (i : Fin r) (t : ℕ) :
    IsIntegral ℤ (D*e*((literalLogPolynomialFilter rho P (Y i)).coeff t).coeff ((N : ℤ)+L)) := by
  rw [literalLogPolynomialFilter_solution_identity C rho Y hY]
  exact logFilter_matrix_product_finite_jet_integral _ Y N L W D e hFlow hYlow hFden hYjet i t

end StrictEUnit
end
