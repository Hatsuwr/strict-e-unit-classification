import ScalarEulerCompanionLogJets
import LogFrameFilteredDenominators

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- A unit top scalar coefficient forces the indicial polynomial to have the
FULL scalar order, rather than merely being a nonzero polynomial. -/
theorem scalarEulerIndicial_full_order (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0) :
    (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).natDegree=r ∧
    scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0≠0 := by
  let P := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0
  have htop : P.coeff r≠0 := by
    have he := scalarEulerCoefficientSymbol_coeff_fin r (fun i k =>PowerSeries.coeff K k (b i)) 0 (Fin.last r)
    change P.coeff r=PowerSeries.coeff K 0 (b (Fin.last r)) at he
    rw [he,PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact hb
  refine ⟨le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero htop),?_⟩
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)
  · intro hz
    exact htop (by rw [show P=0 from hz,Polynomial.coeff_zero])

/-- Cardinality is derived from splitting and the actual top coefficient.
The indexing equivalence is constructed, not an assumed completeness witness. -/
def scalarEulerFrobeniusIndexEquiv (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K)) :
    frobeniusRootSeedIndex (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0) ≃ Fin r :=
  Fintype.equivFinOfCardEq (frobeniusRootSeedIndex_card_order _ hsplit r
    (scalarEulerIndicial_full_order r b hb).1)

/-- A complete companion-jet frame, nonzero determinant and actual inverse are
constructed for a regular scalar Euler equation whose indicial polynomial
splits over K. No actual frame or nonvanishing is supplied as a hypothesis. -/
theorem scalarEuler_constructed_frobenius_frame (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K)) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    let e := scalarEulerFrobeniusIndexEquiv r b hb hsplit
    let rho : Fin r → K := fun j =>frobeniusRootSeedExponent (B 0) (e.symm j)
    let Y := frobeniusActualJetMatrix B e
    Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (scalarEulerPowerSeriesCompanion r b i l)*Y l j) ∧
    ∃ J : Matrix (Fin r) (Fin r) (LaurentSeries (Polynomial K)),∃ W : ℕ,
      (logPolynomialToCoefficientSeries.mapMatrix Y)*J=1 ∧
      J*(logPolynomialToCoefficientSeries.mapMatrix Y)=1 ∧
      (∀ i j a,a< -(W : ℤ) →(J i j).coeff a=0) := by
  dsimp only
  have hdet := frobeniusActualJetMatrix_det_ne_zero _ hsplit (scalarEulerFrobeniusIndexEquiv r b hb hsplit)
  have hY := frobeniusActualJetMatrix_solution r b hb (scalarEulerIndicial_full_order r b hb).2
    (scalarEulerFrobeniusIndexEquiv r b hb hsplit)
  exact ⟨hdet,hY,logFrame_exists_inverse_with_fixed_pole_bound _ _ _ hY hdet⟩

/-- For the constructed frame, filtered arithmetic needs only actual companion
connection arithmetic and exponent binomial arithmetic. No unproved geometric
frame/inverse/degree assumptions survive. Those TWO arithmetic inputs are not
asserted for the original Fourier companion by this theorem. -/
theorem scalarEuler_constructed_filtered_denominators [NumberField K]
    (r : ℕ) (b : Fin (r+1) → PowerSeries K)
    (hb : PowerSeries.constantCoeff K (b (Fin.last r))≠0)
    (hsplit : (scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K))
    (Bnd : ℝ) (hBnd : 1≤Bnd)
    (hden : ∀ M : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤Bnd^(M+1) ∧
      ∀ m,m≤M →∀ l,l≤M →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
        (powerSeriesEulerDividedConnection (scalarEulerPowerSeriesCompanion r b) m i j)))
    (hrho : JointBinomialPrefixDenominators (fun j : Fin r =>frobeniusRootSeedExponent _
      ((scalarEulerFrobeniusIndexEquiv r b hb hsplit).symm j))) :
    let B := scalarEulerCoefficientSymbol r (fun i k =>PowerSeries.coeff K k (b i))
    let e := scalarEulerFrobeniusIndexEquiv r b hb hsplit
    let rho : Fin r → K := fun j =>frobeniusRootSeedExponent (B 0) (e.symm j)
    let Y := frobeniusActualJetMatrix B e
    ∃ L : ℤ,∃ d : ℕ,∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,
      0<D ∧ (D : ℝ)≤E^(N+1) ∧ ∀ m,m≤N →∀ s i t,
      IsIntegral ℤ ((D : K)*((literalLogPolynomialFilter (rho s)
        (allClassPrefixFilter rho L m d) (Y i s)).coeff t).coeff ((m : ℤ)+L)) := by
  obtain ⟨hdet,hY,hJ⟩ := scalarEuler_constructed_frobenius_frame r b hb hsplit
  exact logFrame_filtered_solution_common_denominators _ Bnd hBnd hden _ hrho _ hY hdet

end StrictEUnit
end
