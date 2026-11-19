import LaurentStableSubspaceDescent
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Ideal.Maps

/-!
NEW PROOF RECONSTRUCTION, not recovered original source.

A coefficient-derivative-stable Laurent polynomial ideal is extended from
its contraction to the constant-coefficient polynomial ring. For each
individual polynomial, only its finite monomial support is used. The
corresponding finite-dimensional coefficient subspace has a literal constant
basis by `laurent_stable_subspace_constant_basis`.

No hypothesis asserts constant generation, an ideal descent conclusion,
primality, or injectivity of numerical evaluation.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators

namespace StrictEUnit

variable {K σ : Type*} [Field K] [CharZero K]

/-- Apply the actual ordinary Laurent derivative to polynomial coefficients.
The additive-hom structure is definitionally the one used by the frozen
`OrdinaryPointPolynomialIdealGauge` caller. -/
def laurentMvCoeffDerivative :
    MvPolynomial σ (LaurentSeries K) →+ MvPolynomial σ (LaurentSeries K) :=
  Finsupp.mapRange.addMonoidHom
    { toFun := fun x => laurentOrdinaryDerivation x
      map_zero' := (laurentOrdinaryDerivation (k := K)).map_zero
      map_add' := fun x y => (laurentOrdinaryDerivation (k := K)).map_add x y }

@[simp] theorem laurentMvCoeffDerivative_coeff
    (P : MvPolynomial σ (LaurentSeries K)) (m : σ →₀ ℕ) :
    MvPolynomial.coeff m (laurentMvCoeffDerivative P) =
      laurentOrdinaryDerivation (MvPolynomial.coeff m P) := rfl

@[simp] theorem laurentMvCoeffDerivative_monomial
    (m : σ →₀ ℕ) (a : LaurentSeries K) :
    laurentMvCoeffDerivative (MvPolynomial.monomial m a) =
      MvPolynomial.monomial m (laurentOrdinaryDerivation a) := by
  exact Finsupp.mapRange_single
    (f := fun x : LaurentSeries K => laurentOrdinaryDerivation x)
    (hf := (laurentOrdinaryDerivation (k := K)).map_zero)

/-- Encode a vector as a polynomial with a specified finite list of monomials.
No injectivity or distinctness of the list is needed. -/
private def finiteMonomialVector {R : Type*} [CommSemiring R] {n : ℕ}
    (m : Fin n → σ →₀ ℕ) :
    (Fin n → R) →ₗ[R] MvPolynomial σ R :=
  ∑ i, (MvPolynomial.monomial (m i)).comp (LinearMap.proj i)

private theorem finiteMonomialVector_apply
    {R : Type*} [CommSemiring R] {n : ℕ}
    (m : Fin n → σ →₀ ℕ) (v : Fin n → R) :
    finiteMonomialVector m v = ∑ i, MvPolynomial.monomial (m i) (v i) := by
  simp only [finiteMonomialVector, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

private theorem finiteMonomialVector_derivative {n : ℕ}
    (m : Fin n → σ →₀ ℕ) (v : Fin n → LaurentSeries K) :
    laurentMvCoeffDerivative (finiteMonomialVector m v) =
      finiteMonomialVector m (fun i => laurentOrdinaryDerivation (v i)) := by
  simp only [finiteMonomialVector_apply, map_sum,
    laurentMvCoeffDerivative_monomial]

/-- On any fixed finite list of monomials, ideal membership descends from
Laurent coefficients to constant coefficients. This is derived from
derivative invariance, not assumed. -/
private theorem finiteMonomialVector_mem_constant_extension {n : ℕ}
    (J : Ideal (MvPolynomial σ (LaurentSeries K)))
    (hJ : ∀ P, P ∈ J → laurentMvCoeffDerivative P ∈ J)
    (m : Fin n → σ →₀ ℕ) (v : Fin n → LaurentSeries K)
    (hv : finiteMonomialVector m v ∈ J) :
    finiteMonomialVector m v ∈
      (J.comap (MvPolynomial.map (algebraMap K (LaurentSeries K)))).map
        (MvPolynomial.map (algebraMap K (LaurentSeries K))) := by
  classical
  let φ : MvPolynomial σ K →+* MvPolynomial σ (LaurentSeries K) :=
    MvPolynomial.map (algebraMap K (LaurentSeries K))
  let J₀ : Ideal (MvPolynomial σ (LaurentSeries K)) := (J.comap φ).map φ
  let E : Submodule (LaurentSeries K) (Fin n → LaurentSeries K) :=
    (J.restrictScalars (LaurentSeries K)).comap (finiteMonomialVector m)
  have hstable : ∀ w : Fin n → LaurentSeries K, w ∈ E →
      (fun i => laurentOrdinaryDerivation (w i)) ∈ E := by
    intro w hw
    change finiteMonomialVector m w ∈ J at hw
    change finiteMonomialVector m (fun i => laurentOrdinaryDerivation (w i)) ∈ J
    rw [← finiteMonomialVector_derivative]
    exact hJ _ hw
  obtain ⟨s, _hs, _hdim, _p, b, hconstant, _hpivot, hspan⟩ :=
    laurent_stable_subspace_constant_basis E hstable
  have hle : E ≤
      (J₀.restrictScalars (LaurentSeries K)).comap (finiteMonomialVector m) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change finiteMonomialVector m (b i : Fin n → LaurentSeries K) ∈ J₀
    let q : MvPolynomial σ K := finiteMonomialVector m
      (fun j => ((b i : Fin n → LaurentSeries K) j).coeff 0)
    have hq : φ q = finiteMonomialVector m (b i : Fin n → LaurentSeries K) := by
      change MvPolynomial.map (algebraMap K (LaurentSeries K))
        (finiteMonomialVector m
          (fun j => ((b i : Fin n → LaurentSeries K) j).coeff 0)) = _
      rw [finiteMonomialVector_apply, finiteMonomialVector_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [MvPolynomial.map_monomial]
      exact congrArg (MvPolynomial.monomial (m j)) (hconstant i j).symm
    have hqJ : q ∈ J.comap φ := by
      change φ q ∈ J
      rw [hq]
      exact (b i).property
    rw [← hq]
    exact Ideal.mem_map_of_mem φ hqJ
  exact hle hv

/-- Every ideal preserved by the actual coefficientwise ordinary Laurent
derivative is the extension of its contraction to constant polynomials.
The proof works for any variable type, since each polynomial has finite
support. -/
theorem laurent_stable_polynomial_ideal_constant_descent
    (J : Ideal (MvPolynomial σ (LaurentSeries K)))
    (hJ : ∀ P, P ∈ J → laurentMvCoeffDerivative P ∈ J) :
    (J.comap (MvPolynomial.map (algebraMap K (LaurentSeries K)))).map
      (MvPolynomial.map (algebraMap K (LaurentSeries K))) = J := by
  classical
  apply le_antisymm Ideal.map_comap_le
  intro P hP
  let e : Fin P.support.card ≃ P.support := P.support.equivFin.symm
  let m : Fin P.support.card → σ →₀ ℕ := fun i => (e i).val
  let v : Fin P.support.card → LaurentSeries K := fun i => MvPolynomial.coeff (m i) P
  have hrep : finiteMonomialVector m v = P := by
    rw [finiteMonomialVector_apply]
    change (∑ i, MvPolynomial.monomial (e i).val
      (MvPolynomial.coeff (e i).val P)) = P
    rw [e.sum_comp (fun j : P.support =>
      MvPolynomial.monomial j.val (MvPolynomial.coeff j.val P))]
    rw [Finset.sum_coe_sort P.support
      (fun j : σ →₀ ℕ => MvPolynomial.monomial j (MvPolynomial.coeff j P))]
    exact MvPolynomial.support_sum_monomial_coeff P
  rw [← hrep]
  exact finiteMonomialVector_mem_constant_extension J hJ m v (hrep.symm ▸ hP)

end StrictEUnit
end
