import Stage35EntireRelationResidual
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Polynomial.Eval.Coeff

/-! Reconstruct an exact homogeneous polynomial lift from supplied linear
coefficient lifts for a fixed finite homogeneous family. The arithmetic
existence of those coefficient lifts is not asserted. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Topology
namespace StrictEUnit
variable {R S ι σ : Type*} [CommSemiring R] [CommSemiring S] [Fintype ι]

/-- Polynomial coefficient functions combined with fixed homogeneous forms. -/
def homogeneousLiftFromCoefficients
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R) :
    Polynomial (MvPolynomial σ R) :=
  ∑ i, (q i).map MvPolynomial.C * Polynomial.C (Q i)

theorem homogeneousLiftFromCoefficients_coeff
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R) (r : ℕ) :
    (homogeneousLiftFromCoefficients q Q).coeff r =
      ∑ i, MvPolynomial.C ((q i).coeff r) * Q i := by
  simp only [homogeneousLiftFromCoefficients, Polynomial.finset_sum_coeff,
    Polynomial.coeff_mul_C, Polynomial.coeff_map]

theorem homogeneousLiftFromCoefficients_homogeneous
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R) (D : ℕ)
    (hQ : ∀ i, (Q i).IsHomogeneous D) :
    ∀ r, ((homogeneousLiftFromCoefficients q Q).coeff r).IsHomogeneous D := by
  intro r
  rw [homogeneousLiftFromCoefficients_coeff]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact (hQ i).C_mul _

theorem homogeneousLiftFromCoefficients_eval_one
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R) :
    (homogeneousLiftFromCoefficients q Q).eval 1 =
      ∑ i, MvPolynomial.C ((q i).eval 1) * Q i := by
  simp only [homogeneousLiftFromCoefficients, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_one_map]

theorem homogeneousLiftFromCoefficients_eval₂
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R)
    (φ : R →+* S) (v : σ → S) (z : S) :
    Polynomial.eval₂ (MvPolynomial.eval₂Hom φ v) z
      (homogeneousLiftFromCoefficients q Q) =
      ∑ i, (q i).eval₂ φ z * MvPolynomial.eval₂ φ v (Q i) := by
  have hc : (MvPolynomial.eval₂Hom φ v).comp MvPolynomial.C = φ := by
    ext a
    simp
  simp only [homogeneousLiftFromCoefficients, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_map, hc]
  rfl

/-- Exact reconstruction needs the values q_i(1)=p_i, not values up to an
unspecified scalar or a denominator which might vanish at one. -/
theorem homogeneousLiftFromCoefficients_exact
    (q : ι → Polynomial R) (Q : ι → MvPolynomial σ R)
    (p : ι → R) (P : MvPolynomial σ R)
    (hq : ∀ i, (q i).eval 1 = p i)
    (hP : P = ∑ i, MvPolynomial.C (p i) * Q i) :
    (homogeneousLiftFromCoefficients q Q).eval 1 = P := by
  rw [homogeneousLiftFromCoefficients_eval_one, hP]
  simp only [hq]

/-- The literal arithmetic lift once polynomial linear-relation coefficients
are supplied for evaluations of a homogeneous family. This is a reduction,
not the deep theorem that those coefficients exist. -/
theorem homogeneousLift_of_coefficient_relations
    (f : σ → entireFunctionAlgebra)
    (Q : ι → MvPolynomial σ AlgebraicComplex) (D : ℕ)
    (hQ : ∀ i, (Q i).IsHomogeneous D)
    (p : ι → AlgebraicComplex) (P : MvPolynomial σ AlgebraicComplex)
    (hP : P = ∑ i, MvPolynomial.C (p i) * Q i)
    (q : ι → Polynomial AlgebraicComplex)
    (hq : ∀ i, (q i).eval 1 = p i)
    (hrel : ∀ z : ℂ, ∑ i,
      (q i).eval₂ (algebraicClosure ℚ ℂ).val.toRingHom z *
        MvPolynomial.eval₂ (algebraicClosure ℚ ℂ).val.toRingHom
          (fun j => (f j).val z) (Q i) = 0) :
    ∃ H : Polynomial (MvPolynomial σ AlgebraicComplex),
      (∀ r, (H.coeff r).IsHomogeneous D) ∧
      stage35_relationResidual f H =ᶠ[𝓝 (1 : ℂ)] 0 ∧ H.eval 1 = P := by
  refine ⟨homogeneousLiftFromCoefficients q Q,
    homogeneousLiftFromCoefficients_homogeneous q Q D hQ, ?_,
    homogeneousLiftFromCoefficients_exact q Q p P hq hP⟩
  apply Filter.Eventually.of_forall
  intro z
  exact (homogeneousLiftFromCoefficients_eval₂ q Q
    (algebraicClosure ℚ ℂ).val.toRingHom (fun j => (f j).val z) z).trans (hrel z)

/-- Normalize by a nonzero algebraic scalar, never by a function vanishing
at the specialization point. -/
def normalizedHomogeneousLift {K : Type*} [Field K]
    (c : K) (H : Polynomial (MvPolynomial σ K)) : Polynomial (MvPolynomial σ K) :=
  Polynomial.C (MvPolynomial.C c⁻¹) * H

theorem normalizedHomogeneousLift_homogeneous {K : Type*} [Field K]
    (c : K) (H : Polynomial (MvPolynomial σ K)) (D : ℕ)
    (hH : ∀ r, (H.coeff r).IsHomogeneous D) :
    ∀ r, ((normalizedHomogeneousLift c H).coeff r).IsHomogeneous D := by
  intro r
  rw [normalizedHomogeneousLift, Polynomial.coeff_C_mul]
  exact (hH r).C_mul _

theorem normalizedHomogeneousLift_exact {K : Type*} [Field K]
    (c : K) (hc : c ≠ 0) (H : Polynomial (MvPolynomial σ K))
    (P : MvPolynomial σ K) (hH : H.eval 1 = MvPolynomial.C c * P) :
    (normalizedHomogeneousLift c H).eval 1 = P := by
  rw [normalizedHomogeneousLift, Polynomial.eval_mul, Polynomial.eval_C, hH,
    ← mul_assoc, ← MvPolynomial.C_mul, inv_mul_cancel₀ hc, map_one, one_mul]

/-- A cleared lift specializing to s(1)P can be normalized exactly only when
s(1) is nonzero. This condition is retained explicitly. -/
theorem homogeneousLift_normalize_regular_clearing
    (f : σ → entireFunctionAlgebra)
    (s : Polynomial AlgebraicComplex) (hs : s.eval 1 ≠ 0)
    (H : Polynomial (MvPolynomial σ AlgebraicComplex))
    (P : MvPolynomial σ AlgebraicComplex) (D : ℕ)
    (hH : ∀ r, (H.coeff r).IsHomogeneous D)
    (hrel : stage35_relationResidual f H =ᶠ[𝓝 (1 : ℂ)] 0)
    (hexact : H.eval 1 = MvPolynomial.C (s.eval 1) * P) :
    ∃ G : Polynomial (MvPolynomial σ AlgebraicComplex),
      (∀ r, (G.coeff r).IsHomogeneous D) ∧
      stage35_relationResidual f G =ᶠ[𝓝 (1 : ℂ)] 0 ∧ G.eval 1 = P := by
  refine ⟨normalizedHomogeneousLift (s.eval 1) H,
    normalizedHomogeneousLift_homogeneous _ H D hH, ?_,
    normalizedHomogeneousLift_exact _ hs H P hexact⟩
  filter_upwards [hrel] with z hz
  unfold stage35_relationResidual at hz ⊢
  rw [normalizedHomogeneousLift, Polynomial.eval₂_mul, Polynomial.eval₂_C, hz]
  simp only [Pi.zero_apply, mul_zero]

theorem homogeneousLift_ne_zero_of_exact {K : Type*} [CommSemiring K]
    (H : Polynomial (MvPolynomial σ K)) (P : MvPolynomial σ K)
    (hP : P ≠ 0) (hH : H.eval 1 = P) : H ≠ 0 := by
  intro hzero
  apply hP
  rw [← hH, hzero, Polynomial.eval_zero]

end StrictEUnit
