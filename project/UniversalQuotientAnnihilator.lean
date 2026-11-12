import UniversalFormalEvaluation
import FunctionalIdealAnnihilatorTransfer
import OrdinaryScaledProductInitialZero

/-! The exact ordinary annihilator of the scaled source product transfers
through the constructed universal evaluation. Its no-pole consequence forces
a distinguished variable into the prime constant ideal. No minimality of an
operator or injectivity of a tensor-to-series map is assumed. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

section ScalarTranslation
variable {K H : Type*} [Field K] [Field H]

/-- The coefficient map retains the exact translated rational embedding. -/
def universalTranslatedRationalMap (f : K →+* H) (α : K) :
    RatFunc K →+* LaurentSeries H :=
  (universalLaurentMap f).comp (ordinaryPointRationalMap α)

theorem universalTranslatedRationalMap_polynomial
    (f : K →+* H) (α : K) (p : Polynomial K) :
    universalTranslatedRationalMap f α (algebraMap (Polynomial K) (RatFunc K) p) =
      HahnSeries.ofPowerSeries ℤ H
        (PowerSeries.map f (ordinaryPointPolynomialSeries α p)) := by
  change universalLaurentMap f
    (ordinaryPointRationalMap α (algebraMap (Polynomial K) (RatFunc K) p)) = _
  rw [ordinaryPointRationalMap_polynomial, ← ordinaryPointPolynomialSeries_coe,
    universalLaurentMap_ofPowerSeries]

theorem universalTranslatedPolynomial_constantCoeff
    (f : K →+* H) (α : K) (p : Polynomial K) :
    PowerSeries.constantCoeff H (PowerSeries.map f (ordinaryPointPolynomialSeries α p)) =
      f (p.eval α) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ordinaryPointPolynomialSeries_constantCoeff]

theorem universalTranslatedPolynomial_constantCoeff_ne_zero
    (f : K →+* H) (α : K) (p : Polynomial K) (hp : p.eval α ≠ 0) :
    PowerSeries.constantCoeff H (PowerSeries.map f (ordinaryPointPolynomialSeries α p)) ≠ 0 := by
  rw [universalTranslatedPolynomial_constantCoeff]
  exact (map_ne_zero f).mpr hp

/-- The rational function (z-α)⁻¹, before any Laurent embedding. -/
def ordinaryPointInverseLinear (α : K) : RatFunc K :=
  (algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α))⁻¹

theorem ordinaryPointPolynomialSeries_sub_point (α : K) :
    ordinaryPointPolynomialSeries α (Polynomial.X - Polynomial.C α) =
      (PowerSeries.X : PowerSeries K) := by
  change (((Polynomial.X - Polynomial.C α).comp
    (Polynomial.X + Polynomial.C α) : Polynomial K) : PowerSeries K) = _
  rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    add_sub_cancel_right, Polynomial.coe_X]

theorem universalTranslatedRationalMap_inverseLinear
    (f : K →+* H) (α : K) :
    universalTranslatedRationalMap f α (ordinaryPointInverseLinear α) =
      (HahnSeries.ofPowerSeries ℤ H (PowerSeries.X : PowerSeries H))⁻¹ := by
  rw [ordinaryPointInverseLinear, map_inv₀,
    universalTranslatedRationalMap_polynomial, ordinaryPointPolynomialSeries_sub_point,
    PowerSeries.map_X]

theorem universalTranslatedRationalMap_derivative [CharZero K] [CharZero H]
    (f : K →+* H) (α : K) (a : RatFunc K) :
    laurentOrdinaryAddDerivative (universalTranslatedRationalMap f α a) =
      universalTranslatedRationalMap f α (rationalOrdinaryAddDerivative a) := by
  change laurentOrdinaryAddDerivative (universalLaurentMap f (ordinaryPointRationalMap α a)) = _
  rw [universalLaurentMap_derivative, ordinaryPointRationalMap_addDerivative]
  rfl

end ScalarTranslation

section ExactAnnihilator
variable {K S : Type*} [Field K] [CharZero K] [Fintype S] {r : ℕ}

/-- A genuine ordinary annihilator of the exact source quotient product
forces a distinguished coordinate into the constant ideal. The same p, y,
matrix A, clearing t,U, and rational source embedding are retained throughout.
The index function may repeat coordinates and S need not be nonempty. -/
theorem universal_quotient_annihilator_exists_variable_mem
    (y : Fin r → LaurentSeries K)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (hsystem : ∀ i, laurentOrdinaryDerivation (y i) =
      ∑ j, algebraMap (RatFunc K) (LaurentSeries K) (A i j) * y j)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (ht : t.eval 1 ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (J0 : Ideal (MvPolynomial (Fin r) K)) [J0.IsPrime]
    (hdescent : J0.map (MvPolynomial.map (algebraMap K (LaurentSeries K))) =
      ordinaryPointGaugedIdeal t U (1 : K)
        (mvFunctionalIdeal (algebraMap (RatFunc K) (LaurentSeries K)) y))
    (idx : S → Fin r) (m : ℕ) (p : Fin (m+1) → Polynomial K)
    (hord : (p (Fin.last m)).eval 1 ≠ 0)
    (hsource : (∑ i, algebraMap (Polynomial K) (LaurentSeries K) (p i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val]
        (algebraMap (RatFunc K) (LaurentSeries K) (ordinaryPointInverseLinear (1 : K)) *
          ∏ s, y (idx s))) = 0) :
    ∃ s, MvPolynomial.X (idx s) ∈ J0 := by
  classical
  let H := universalConstantField J0
  letI : CharZero H := universalConstantField_charZero J0
  let q : MvPolynomial (Fin r) K →+* H := universalQuotientMap J0
  let f : K →+* H := q.comp MvPolynomial.C
  let g : RatFunc K →+* LaurentSeries H := universalTranslatedRationalMap f (1 : K)
  let v : Fin r → LaurentSeries H :=
    fun i => universalOriginalEval q t U (1 : K) (MvPolynomial.X i)
  let w : S → PowerSeries H := fun s => universalPowerVector q t U (1 : K) (idx s)
  let b : Fin (m+1) → PowerSeries H :=
    fun i => PowerSeries.map f (ordinaryPointPolynomialSeries (1 : K) (p i))
  let c : Fin (m+1) → RatFunc K :=
    fun i => algebraMap (Polynomial K) (RatFunc K) (p i)
  let P : MvPolynomial (Fin r) (RatFunc K) := ∏ s, MvPolynomial.X (idx s)
  let a : RatFunc K := ordinaryPointInverseLinear (1 : K)
  have hev : universalOriginalEval q t U (1 : K) = MvPolynomial.eval₂Hom g v :=
    universalOriginalEval_eq_eval₂Hom q t U (1 : K)
  have hv (i : Fin r) : laurentOrdinaryAddDerivative (v i) =
      ∑ j, g (A i j) * v j :=
    universalOriginalEval_system q A t U (1 : K) ht hclear i
  have hkernel : mvFunctionalIdeal (algebraMap (RatFunc K) (LaurentSeries K)) y ≤
      mvFunctionalIdeal g v := by
    intro Q hQ
    change MvPolynomial.eval₂Hom g v Q = 0
    rw [← hev]
    exact universalOriginalEval_kills_relation t U (1 : K)
      (mvFunctionalIdeal (algebraMap (RatFunc K) (LaurentSeries K)) y)
      J0 hdescent Q hQ
  have hsource' : (∑ i, algebraMap (RatFunc K) (LaurentSeries K) (c i) *
      (laurentOrdinaryAddDerivative (K := K) : LaurentSeries K → LaurentSeries K)^[i.val]
        (algebraMap (RatFunc K) (LaurentSeries K) a *
          MvPolynomial.eval₂Hom (algebraMap (RatFunc K) (LaurentSeries K)) y P)) = 0 := by
    simpa only [c, a, P, map_prod, MvPolynomial.eval₂Hom_X',
      ← IsScalarTower.algebraMap_apply (Polynomial K) (RatFunc K) (LaurentSeries K)]
      using hsource
  have htransfer := functionalIdeal_scaled_annihilator_transfer
    (rationalOrdinaryAddDerivative (K := K))
    (laurentOrdinaryAddDerivative (K := K)) (laurentOrdinaryAddDerivative (K := H))
    rationalOrdinaryAddDerivative_one rationalOrdinaryAddDerivative_mul
    laurentOrdinaryAddDerivative_mul laurentOrdinaryAddDerivative_mul
    (algebraMap (RatFunc K) (LaurentSeries K)) g
    stage14_rationalLaurent_differential (universalTranslatedRationalMap_derivative f (1 : K))
    A y v hsystem hv hkernel a P m c hsource'
  have hb (i : Fin (m+1)) : g (c i) = HahnSeries.ofPowerSeries ℤ H (b i) :=
    universalTranslatedRationalMap_polynomial f (1 : K) (p i)
  have ha : g a = (HahnSeries.ofPowerSeries ℤ H (PowerSeries.X : PowerSeries H))⁻¹ :=
    universalTranslatedRationalMap_inverseLinear f (1 : K)
  have hP : MvPolynomial.eval₂Hom g v P =
      HahnSeries.ofPowerSeries ℤ H (∏ s, w s) := by
    simp only [P, map_prod, MvPolynomial.eval₂Hom_X', v, w,
      universalOriginalEval_X_eq_ofPowerSeries]
  have htarget : (∑ i, HahnSeries.ofPowerSeries ℤ H (b i) *
      (laurentOrdinaryDerivation : LaurentSeries H → LaurentSeries H)^[i.val]
        ((HahnSeries.ofPowerSeries ℤ H (PowerSeries.X : PowerSeries H))⁻¹ *
          HahnSeries.ofPowerSeries ℤ H (∏ s, w s))) = 0 := by
    simpa only [hb, ha, hP] using htransfer
  have hbOrd : PowerSeries.constantCoeff H (b (Fin.last m)) ≠ 0 :=
    universalTranslatedPolynomial_constantCoeff_ne_zero f (1 : K) (p (Fin.last m)) hord
  obtain ⟨s, hs⟩ := ordinary_scaled_product_exists_constant_zero w m b hbOrd htarget
  refine ⟨s, (universalQuotientMap_eq_zero_iff J0 (MvPolynomial.X (idx s))).mp ?_⟩
  simpa only [w, universalPowerVector_constantCoeff, q] using hs

end ExactAnnihilator
end StrictEUnit
end
