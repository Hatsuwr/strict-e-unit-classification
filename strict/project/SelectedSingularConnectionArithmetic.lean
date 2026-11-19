import SingularConnectionLaurentArithmetic
import SelectedFuchsSourceData

/-! The full original divided-connection arithmetic is transported to the
original singular-center germs and Laurent expansions. This is source
operator arithmetic, NOT an assertion about the Fourier solution basis. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [NumberField K]

def SameClearingSingularConnectionArithmeticData (r : ℕ) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K))) (E : ℝ) : Prop :=
  let t := T.map (algebraMap (𝓞 K) K)
  let U : Matrix (Fin r) (Fin r) (Polynomial K) :=
    fun i j => (UI i j).map (algebraMap (𝓞 K) K)
  let v := T.coeff t.natTrailingDegree
  let q := Int.natAbs (Algebra.norm ℤ v)
  let R : ℕ → Matrix (Fin r) (Fin r) (LaurentSeries K) := fun m i j =>
    algebraMap (RatFunc K) (LaurentSeries K) ((m.factorial : RatFunc K)⁻¹*
      matrixConnectionSequence stage14_rationalOrdinaryDerivation (minimalDerivativeCompanion r c) m i j)
  (∀ m i j,(t : PowerSeries K)^m*samePoleClearedDividedConnectionGerm t U m i j=
    (PowerSeries.X : PowerSeries K)^(t.natTrailingDegree*m)*
      (dividedPolynomialConnectionSequence t U m i j : PowerSeries K)) ∧
  (∀ m i j,HahnSeries.ofPowerSeries ℤ K (samePoleClearedDividedConnectionGerm t U m i j)=
    (HahnSeries.ofPowerSeries ℤ K PowerSeries.X)^(t.natTrailingDegree*m)*R m i j) ∧
  0<q ∧ 1≤(q : ℝ)*E ∧
  (∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤((q : ℝ)*E)^(N+1) ∧
    ∀ m l,m+l≤N → ∀ i j,IsIntegral ℤ ((D : K)*
      PowerSeries.coeff K l (samePoleClearedDividedConnectionGerm t U m i j))) ∧
  1≤((q : ℝ)*E)^(t.natTrailingDegree+2) ∧
  ∀ N : ℕ,∃ D : ℕ,0<D ∧
    (D : ℝ)≤(((q : ℝ)*E)^(t.natTrailingDegree+2))^(N+1) ∧
      ∀ m,m≤N → ∀ k : ℤ,k≤(N : ℤ) → ∀ i j,IsIntegral ℤ ((D : K)*(R m i j).coeff k)

theorem same_integral_clearing_singular_connection_arithmetic
    (r : ℕ) (c : Fin r → RatFunc K) (T : Polynomial (𝓞 K))
    (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (hT : T.map (algebraMap (𝓞 K) K)≠0)
    (hclear : ∀ i j,algebraMap (Polynomial K) (RatFunc K)
      ((UI i j).map (algebraMap (𝓞 K) K))=
        algebraMap (Polynomial K) (RatFunc K) (T.map (algebraMap (𝓞 K) K))*
          minimalDerivativeCompanion r c i j)
    (E : ℝ) (hE : 1≤E)
    (hden : ∀ N : ℕ,∃ delta : ℕ,0<delta ∧ (delta : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ i j k,IsIntegral ℤ ((delta : K)*
        (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K))
          (fun i j => (UI i j).map (algebraMap (𝓞 K) K)) m i j).coeff k)) :
    SameClearingSingularConnectionArithmeticData r c T UI E := by
  unfold SameClearingSingularConnectionArithmeticData
  intro t U v q R
  let H := fun m (ij : Fin r × Fin r) => dividedPolynomialConnectionSequence t U m ij.1 ij.2
  have hdenH : ∀ N : ℕ,∃ delta : ℕ,0<delta ∧ (delta : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ ij k,IsIntegral ℤ ((delta : K)*(H m ij).coeff k) := by
    intro N
    obtain ⟨delta,hd,hdb,hdi⟩ := hden N
    exact ⟨delta,hd,hdb,fun m hm ij k => hdi m hm ij.1 ij.2 k⟩
  obtain ⟨hq,hqE,htri⟩ := poleClearedPolynomialQuotientGerm_common_denominators T H hT E hE hdenH
  have hid (m : ℕ) (ij : Fin r × Fin r) :=
    samePoleClearedDividedConnectionGerm_rational_identity
      (minimalDerivativeCompanion r c) t U hT hclear m ij.1 ij.2
  have hl := bivariate_germ_denominators_laurent_prefix
    (fun m (ij : Fin r × Fin r) => samePoleClearedDividedConnectionGerm t U m ij.1 ij.2)
    (fun m (ij : Fin r × Fin r) => R m ij.1 ij.2) t.natTrailingDegree hid
    ((q : ℝ)*E) hqE htri
  refine ⟨samePoleClearedDividedConnectionGerm_clearing t U hT,
    fun m i j => hid m (i,j),hq,hqE,?_,hl.1,?_⟩
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := htri N
    exact ⟨D,hD,hDb,fun m l hml i j => hDi m l hml (i,j)⟩
  · intro N
    obtain ⟨D,hD,hDb,hDi⟩ := hl.2 N
    exact ⟨D,hD,hDb,fun m hm k hk i j => hDi m hm k hk (i,j)⟩

/-- Original source arithmetic, rather than an assumed Fourier cancellation
condition, discharges every hypothesis. Ordinary zero is included. -/
theorem selectedFuchsSourceData_singular_connection_arithmetic
    (G : PowerSeries K) (a : ℕ → AlgebraicComplex) (phi : K →+* AlgebraicComplex)
    (r : ℕ) (hr : 0<r) (c : Fin r → RatFunc K)
    (T : Polynomial (𝓞 K)) (UI : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)))
    (E : ℝ) (hsource : SelectedFuchsSourceData G a phi r hr c T UI E) :
    SameClearingSingularConnectionArithmeticData r c T UI E := by
  obtain ⟨hdata,hT,hclear,htop,hqn,hann,hmin,hE,hden,hrest⟩ := hsource
  exact same_integral_clearing_singular_connection_arithmetic r c T UI hT hclear E hE hden

end StrictEUnit
end
