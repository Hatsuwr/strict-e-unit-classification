import V5BroadActualRegularity
import Stage20ArithmeticFrameLifting
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Laurent

noncomputable section
namespace StrictEUnit
open Polynomial

theorem v5_polynomial_only_origin_monomial (P : Polynomial AlgebraicComplex)
    (h : ∀ z : ℂ, z ≠ 0 → P.eval₂ (algebraMap AlgebraicComplex ℂ) z ≠ 0) :
    P = C P.leadingCoeff * X ^ P.natDegree := by
  classical
  let φ := algebraMap AlgebraicComplex ℂ
  let Q := P.map φ
  have hQ : Q ≠ 0 := by
    intro hz
    have := h 1 one_ne_zero
    apply this
    rw [← eval_map]
    change Q.eval 1 = 0
    rw [hz, eval_zero]
  have hr : ∀ a ∈ Q.roots, a = 0 := by
    intro a ha
    apply Classical.byContradiction
    intro hn
    apply h a hn
    simpa only [Q, Polynomial.IsRoot, eval_map] using (mem_roots hQ).mp ha
  have hs := IsAlgClosed.splits Q
  have he : Q = C Q.leadingCoeff * X ^ Q.natDegree := by
    conv_lhs => rw [eq_prod_roots_of_splits_id hs]
    have hm : Q.roots.map (fun a => X - C a) = Q.roots.map (fun _ => (X : Polynomial ℂ)) :=
      Multiset.map_congr rfl (fun a ha => by rw [hr a ha]; simp)
    rw [hm]
    simp only [Multiset.map_const', Multiset.prod_replicate]
    have hc : Q.natDegree = Q.roots.card := by simpa using natDegree_eq_card_roots hs
    rw [hc]
  apply Polynomial.map_injective φ φ.injective
  simpa [Q, φ] using he

theorem v5_polynomial_only_origin_laurent_inverse (P : Polynomial AlgebraicComplex)
    (h : ∀ z : ℂ, z ≠ 0 → P.eval₂ (algebraMap AlgebraicComplex ℂ) z ≠ 0) :
    ∃ L : LaurentPolynomial AlgebraicComplex, ∀ z : ℂˣ,
      arithmeticLaurentEvaluation z L * P.eval₂ (algebraMap AlgebraicComplex ℂ) (z : ℂ) = 1 := by
  classical
  have hp : P ≠ 0 := by
    intro he
    simpa [he] using h 1 one_ne_zero
  have hc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have he := v5_polynomial_only_origin_monomial P h
  refine ⟨LaurentPolynomial.C P.leadingCoeff⁻¹ *
    LaurentPolynomial.T (-(P.natDegree : ℤ)), ?_⟩
  intro z
  have hev : P.eval₂ (algebraMap AlgebraicComplex ℂ) (z : ℂ) =
      algebraMap AlgebraicComplex ℂ P.leadingCoeff * (z : ℂ) ^ P.natDegree := by
    conv_lhs => rw [he]
    simp
  rw [hev]
  simp only [arithmeticLaurentEvaluation, map_mul, LaurentPolynomial.eval₂_C,
    LaurentPolynomial.eval₂_T_neg_n, map_inv₀, Units.val_inv_eq_inv_val]
  have hc' : ((algebraicClosure ℚ ℂ).val.toRingHom P.leadingCoeff) ≠ 0 :=
    (map_ne_zero (algebraicClosure ℚ ℂ).val.toRingHom).mpr hc
  change ((algebraicClosure ℚ ℂ).val.toRingHom P.leadingCoeff)⁻¹ *
    (z : ℂ)⁻¹ ^ P.natDegree *
    ((algebraicClosure ℚ ℂ).val.toRingHom P.leadingCoeff * (z : ℂ)^P.natDegree) = 1
  rw [inv_pow]
  have hz : (z : ℂ) ≠ 0 := Units.ne_zero z
  field_simp [hc', hz]
  exact div_self (mul_ne_zero hc' (pow_ne_zero _ hz))

#print axioms v5_polynomial_only_origin_monomial
#print axioms v5_polynomial_only_origin_laurent_inverse
end StrictEUnit
