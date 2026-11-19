import V5BroadNormQuotientAnnihilator
import V5ActualWideDivisionEndpoint

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 40000
open scoped BigOperators
namespace StrictEUnit
local instance actualWideQuotientEntireCommRing (k : Subfield ℂ) :
    CommRing (subfieldEntireFunctionAlgebra k) := (subfieldEntireFunctionAlgebra k).toCommRing
local instance actualWideQuotientEntireAddCommMonoid (k : Subfield ℂ) :
    AddCommMonoid (subfieldEntireFunctionAlgebra k) :=
  @NonUnitalNonAssocSemiring.toAddCommMonoid _
    (@NonAssocSemiring.toNonUnitalNonAssocSemiring _
      (@Semiring.toNonAssocSemiring _
        (@CommSemiring.toSemiring _ (subfieldEntireFunctionAlgebra k).toCommSemiring)))



local instance actualWideQuotientEntireAddGroup (k : Subfield ℂ) :
    AddGroup (subfieldEntireFunctionAlgebra k) :=
  @AddCommGroup.toAddGroup _ (@Ring.toAddCommGroup _
    (@CommRing.toRing _ (subfieldEntireFunctionAlgebra k).toCommRing))

theorem v5_actual_wide_quotient_ordinary_annihilator
    (F : subfieldEntireFunctionAlgebra (algebraicClosure ℚ ℂ).toSubfield)
    (hf : V5IsBroadEFunction F.val.val)
    (hzero : F.val.val 1 = 0) (hne : F.val.val ≠ 0) :
    ∃ m : ℕ, ∃ p : Fin (m+1) → Polynomial (algebraicClosure ℚ ℂ).toSubfield,
      0 < m ∧ (p (Fin.last m)).eval 1 ≠ 0 ∧
      ∑ i, algebraMap (Polynomial (algebraicClosure ℚ ℂ).toSubfield) (LaurentSeries (algebraicClosure ℚ ℂ).toSubfield) (p i) *
        (laurentOrdinaryDerivation : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield → LaurentSeries (algebraicClosure ℚ ℂ).toSubfield)^[i.val]
          (v5NormLaurentQuotient F) = 0 := by
  let k := (algebraicClosure ℚ ℂ).toSubfield
  obtain ⟨g,hg,hgf⟩ := v5_actual_wide_division_at_one hf hzero
  have hg0 : g ≠ 0 := by
    intro hz
    apply hne
    funext z
    simpa only [hz, Pi.zero_apply, mul_zero] using (hgf z).symm
  obtain ⟨m,P,hm,hP,hord⟩ := v5_actual_broad_annihilator_over_algebraic hg hg0
  obtain ⟨b,hgd,hgs,_,_⟩ := hg
  let G := v5FactorialEntire g hgd b hgs
  let κ : AlgebraicComplex →+* k :=
    { toFun := fun z => ⟨z.val,z.property⟩
      map_zero' := rfl
      map_one' := rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl }
  let p : Fin (m+1) → Polynomial k := fun i => (P i.val).map κ
  have hpe (j : ℕ) (z : ℂ) : ((P j).map κ).eval₂ k.subtype z =
      (P j).eval₂ (algebraMap AlgebraicComplex ℂ) z := by
    rw [Polynomial.eval₂_map]
    rfl
  have hactual : ∑ i, Polynomial.aeval (subfieldEntireCoordinate k) (p i) *
      (subfieldEntireFunctionDerivation k)^[i.val] G = 0 := by
    apply (stage14_actualPolynomialRelation_iff k G m p).mpr
    intro z
    change (∑ i : Fin (m+1), ((P i.val).map κ).eval₂ k.subtype z * iteratedDeriv i.val g z) = 0
    simp_rw [hpe]
    rw [Fin.sum_univ_eq_sum_range (fun j => (P j).eval₂ (algebraMap AlgebraicComplex ℂ) z * iteratedDeriv j g z)]
    exact hP z
  let φ := stage14_subfieldEntireLaurentAlgHom k
  have hformal : ∑ i, algebraMap (Polynomial (algebraicClosure ℚ ℂ).toSubfield) (LaurentSeries (algebraicClosure ℚ ℂ).toSubfield) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield → LaurentSeries (algebraicClosure ℚ ℂ).toSubfield)^[i.val]
        (φ G) = 0 := by
    have he := congrArg φ hactual
    simpa only [φ, map_sum, map_mul, map_zero, stage14_subfieldEntireLaurentAlgHom_polynomial,
      stage14_subfieldEntireLaurentAlgHom_iterate] using he
  have hmul : (1-subfieldEntireCoordinate k)*G = F := by
    apply Subtype.ext
    apply Subtype.ext
    funext z
    exact hgf z
  let X1 : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield :=
    algebraMap (Polynomial (algebraicClosure ℚ ℂ).toSubfield) (LaurentSeries (algebraicClosure ℚ ℂ).toSubfield) (Polynomial.X-1)
  have hX1 : X1 ≠ 0 := by
    intro hz
    have hpzero : (Polynomial.X-1 : Polynomial k) = 0 :=
      (Polynomial.algebraMap_hahnSeries_injective ℤ) (by simpa only [X1, map_zero] using hz)
    have hh := congrArg (fun q : Polynomial k => q.coeff 1) hpzero
    exact one_ne_zero (by simpa only [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_one, if_neg (by decide : ¬ (1:ℕ)=0), sub_zero, Polynomial.coeff_zero] using hh)
  have hpoly : φ (1-subfieldEntireCoordinate k) = -X1 := by
    simp only [φ, stage14_subfieldEntireLaurentAlgHom_apply, map_sub, map_one,
      subfieldEntireTaylorAlgHom_coordinate]
    dsimp [X1]
    simp only [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_one, map_sub, map_one]
    ring_nf
    rfl
  have hquot : v5NormLaurentQuotient F = -(φ G) := by
    have he := congrArg φ hmul
    rw [map_mul, hpoly] at he
    change X1⁻¹ * φ F = -(φ G)
    rw [← he]
    calc
      _ = -(X1⁻¹ * X1 * φ G) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hX1, one_mul]
  have hneg (j : ℕ) (z : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield) :
      (laurentOrdinaryDerivation : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield → LaurentSeries (algebraicClosure ℚ ℂ).toSubfield)^[j] (-z) =
        -((laurentOrdinaryDerivation : LaurentSeries (algebraicClosure ℚ ℂ).toSubfield → LaurentSeries (algebraicClosure ℚ ℂ).toSubfield)^[j] z) := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, map_neg, Function.iterate_succ_apply']
  refine ⟨m,p,hm,?_,?_⟩
  · intro hz
    apply hord 1 one_ne_zero
    have he := congrArg k.subtype hz
    have heval : k.subtype ((p (Fin.last m)).eval 1) =
        (p (Fin.last m)).eval₂ k.subtype (1 : ℂ) := by
      rw [← Polynomial.eval₂_at_apply, map_one]
    rw [heval, map_zero] at he
    simpa only [p, Fin.val_last, hpe] using he
  · rw [hquot]
    simp_rw [hneg]
    have he := congrArg Neg.neg hformal
    dsimp only at he
    rw [← Finset.sum_neg_distrib] at he
    convert he using 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · exact neg_zero.symm

#print axioms v5_actual_wide_quotient_ordinary_annihilator
end StrictEUnit
