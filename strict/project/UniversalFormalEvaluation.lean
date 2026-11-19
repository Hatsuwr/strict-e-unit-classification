import ActualEntireOrdinaryPrimeGauge
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.Algebra.CharP.Algebra

/-! Universal formal evaluation from the actual constant quotient. The gauge
direction is P(Y) -> P(W X): constant evaluation is composed with that forward
substitution, not with its inverse. All coefficient maps are literal and retain
the same translated rational map. No tensor-product injectivity is used. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators Matrix
namespace StrictEUnit

section ConstantEvaluation
variable {K H ι : Type*} [Field K] [Field H]

def universalLaurentMap (f : K →+* H) : LaurentSeries K →+* LaurentSeries H where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

@[simp] theorem universalLaurentMap_coeff (f : K →+* H)
    (x : LaurentSeries K) (n : ℤ) :
    (universalLaurentMap f x).coeff n = f (x.coeff n) := rfl

@[simp] theorem universalLaurentMap_constant (f : K →+* H) (a : K) :
    universalLaurentMap f (algebraMap K (LaurentSeries K) a) =
      algebraMap H (LaurentSeries H) (f a) := by
  rw [LaurentSeries.algebraMap_apply, LaurentSeries.algebraMap_apply]
  exact HahnSeries.map_C a f

theorem universalLaurentMap_ofPowerSeries (f : K →+* H) (x : PowerSeries K) :
    universalLaurentMap f (HahnSeries.ofPowerSeries ℤ K x) =
      HahnSeries.ofPowerSeries ℤ H (PowerSeries.map f x) := by
  ext n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [universalLaurentMap_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]
  · rw [universalLaurentMap_coeff,
      powerSeries_laurent_coeff_neg _ n (lt_of_not_ge hn), map_zero,
      powerSeries_laurent_coeff_neg _ n (lt_of_not_ge hn)]

def universalConstantEval (q : MvPolynomial ι K →+* H) :
    MvPolynomial ι (LaurentSeries K) →+* LaurentSeries H :=
  MvPolynomial.eval₂Hom (universalLaurentMap (q.comp MvPolynomial.C))
    (fun i => algebraMap H (LaurentSeries H) (q (MvPolynomial.X i)))

theorem universalConstantEval_comp_constants (q : MvPolynomial ι K →+* H) :
    (universalConstantEval q).comp
      (MvPolynomial.map (algebraMap K (LaurentSeries K))) =
    (algebraMap H (LaurentSeries H)).comp q := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, MvPolynomial.map_C,
      universalConstantEval, MvPolynomial.eval₂Hom_C,
      universalLaurentMap_constant]
  · intro i
    simp only [RingHom.comp_apply, MvPolynomial.map_X,
      universalConstantEval, MvPolynomial.eval₂Hom_X']

theorem universalConstantEval_map_constants (q : MvPolynomial ι K →+* H)
    (P : MvPolynomial ι K) :
    universalConstantEval q (MvPolynomial.map (algebraMap K (LaurentSeries K)) P) =
      algebraMap H (LaurentSeries H) (q P) :=
  RingHom.congr_fun (universalConstantEval_comp_constants q) P

variable [CharZero K] [CharZero H]

theorem universalLaurentMap_derivative (f : K →+* H) (x : LaurentSeries K) :
    laurentOrdinaryAddDerivative (universalLaurentMap f x) =
      universalLaurentMap f (laurentOrdinaryAddDerivative x) := by
  ext n
  simp only [laurentOrdinaryAddDerivative_apply, laurentOrdinaryDerivation_coeff,
    universalLaurentMap_coeff, map_mul, map_intCast]

theorem universalConstantEval_differential [Fintype ι]
    (q : MvPolynomial ι K →+* H) (P : MvPolynomial ι (LaurentSeries K)) :
    laurentOrdinaryAddDerivative (universalConstantEval q P) =
      universalConstantEval q (mvCoeffD (laurentOrdinaryAddDerivative (K := K)) P) := by
  refine mvPolynomial_differential_hom
    (mvCoeffD (laurentOrdinaryAddDerivative (K := K)))
    (laurentOrdinaryAddDerivative (K := H))
    (mvCoeffD_mul _ laurentOrdinaryAddDerivative_mul)
    laurentOrdinaryAddDerivative_mul (universalConstantEval q) ?_ ?_ P
  · intro a
    simp only [universalConstantEval, MvPolynomial.eval₂Hom_C, mvCoeffD_C]
    exact universalLaurentMap_derivative (q.comp MvPolynomial.C) a
  · intro i
    rw [mvCoeffD_X _ laurentOrdinaryAddDerivative_one, map_zero]
    simp only [universalConstantEval, MvPolynomial.eval₂Hom_X',
      laurentOrdinaryAddDerivative_apply]
    exact (laurentOrdinaryDerivation (k := H)).map_algebraMap _

end ConstantEvaluation

section Quotient
variable {K ι : Type*} [Field K]

abbrev universalConstantRing (J0 : Ideal (MvPolynomial ι K)) :=
  MvPolynomial ι K ⧸ J0

abbrev universalConstantField (J0 : Ideal (MvPolynomial ι K)) :=
  FractionRing (universalConstantRing J0)

def universalQuotientMap (J0 : Ideal (MvPolynomial ι K)) :
    MvPolynomial ι K →+* universalConstantField J0 :=
  (algebraMap (universalConstantRing J0) (universalConstantField J0)).comp
    (Ideal.Quotient.mk J0)

theorem universalQuotientMap_eq_zero_iff
    (J0 : Ideal (MvPolynomial ι K)) [J0.IsPrime] (P : MvPolynomial ι K) :
    universalQuotientMap J0 P = 0 ↔ P ∈ J0 := by
  change algebraMap (universalConstantRing J0) (universalConstantField J0)
    (Ideal.Quotient.mk J0 P) = 0 ↔ P ∈ J0
  constructor
  · intro h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective (universalConstantRing J0)
      (universalConstantField J0)) (by simpa only [map_zero] using h)
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

theorem universalConstantEval_kills_extension
    (J0 : Ideal (MvPolynomial ι K)) [J0.IsPrime] :
    J0.map (MvPolynomial.map (algebraMap K (LaurentSeries K))) ≤
      RingHom.ker (universalConstantEval (universalQuotientMap J0)) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro P hP
  change universalConstantEval (universalQuotientMap J0)
    (MvPolynomial.map (algebraMap K (LaurentSeries K)) P) = 0
  rw [universalConstantEval_map_constants,
    (universalQuotientMap_eq_zero_iff J0 P).mpr hP, map_zero]

theorem universalConstantField_charZero [CharZero K]
    (J0 : Ideal (MvPolynomial ι K)) [J0.IsPrime] :
    CharZero (universalConstantField J0) :=
  charZero_of_injective_ringHom
    ((universalQuotientMap J0).comp MvPolynomial.C).injective

end Quotient

section OriginalEvaluation
variable {K H : Type*} [Field K] [Field H] [CharZero K] [CharZero H] {r : ℕ}

def universalOriginalEval (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    MvPolynomial (Fin r) (RatFunc K) →+* LaurentSeries H :=
  (universalConstantEval q).comp
    ((matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)).toRingHom.comp
      (MvPolynomial.map (ordinaryPointRationalMap α)))

@[simp] theorem universalOriginalEval_C (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (a : RatFunc K) :
    universalOriginalEval q t U α (MvPolynomial.C a) =
      universalLaurentMap (q.comp MvPolynomial.C) (ordinaryPointRationalMap α a) := by
  change universalConstantEval q
    (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)
      (MvPolynomial.map (ordinaryPointRationalMap α) (MvPolynomial.C a))) =
    universalLaurentMap (q.comp MvPolynomial.C) (ordinaryPointRationalMap α a)
  rw [MvPolynomial.map_C, matrixPolynomialSubst_C]
  exact MvPolynomial.eval₂Hom_C
    (universalLaurentMap (q.comp MvPolynomial.C))
    (fun i => algebraMap H (LaurentSeries H) (q (MvPolynomial.X i)))
    (ordinaryPointRationalMap α a)

theorem universalOriginalEval_X (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (i : Fin r) :
    universalOriginalEval q t U α (MvPolynomial.X i) =
      ∑ j, universalLaurentMap (q.comp MvPolynomial.C)
        (ordinaryPointLaurentFundamental t U α i j) *
        algebraMap H (LaurentSeries H) (q (MvPolynomial.X j)) := by
  change universalConstantEval q
    (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)
      (MvPolynomial.map (ordinaryPointRationalMap α) (MvPolynomial.X i))) =
    ∑ j, universalLaurentMap (q.comp MvPolynomial.C)
      (ordinaryPointLaurentFundamental t U α i j) *
      algebraMap H (LaurentSeries H) (q (MvPolynomial.X j))
  rw [MvPolynomial.map_X, matrixPolynomialSubst_X]
  simp only [universalConstantEval, matrixLinearForm, map_sum, map_mul,
    MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

def universalPowerVector (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (i : Fin r) : PowerSeries H :=
  ∑ j, PowerSeries.map (q.comp MvPolynomial.C)
    (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j) *
    PowerSeries.C H (q (MvPolynomial.X j))

theorem universalOriginalEval_X_eq_ofPowerSeries
    (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (i : Fin r) :
    universalOriginalEval q t U α (MvPolynomial.X i) =
      HahnSeries.ofPowerSeries ℤ H (universalPowerVector q t U α i) := by
  rw [universalOriginalEval_X]
  simp only [universalPowerVector, map_sum, map_mul,
    HahnSeries.ofPowerSeries_C, ordinaryPointLaurentFundamental, Matrix.map_apply,
    universalLaurentMap_ofPowerSeries, LaurentSeries.algebraMap_apply]

theorem universalPowerVector_constantCoeff
    (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (i : Fin r) :
    PowerSeries.constantCoeff H (universalPowerVector q t U α i) =
      q (MvPolynomial.X i) := by
  classical
  simp only [universalPowerVector, map_sum, map_mul, PowerSeries.constantCoeff_C]
  have hw (j : Fin r) :
      PowerSeries.constantCoeff H
        (PowerSeries.map (q.comp MvPolynomial.C)
          (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j)) =
        if i = j then 1 else 0 := by
    have hij : PowerSeries.constantCoeff K
        (formalFundamentalMatrix (ordinaryPointClearedMatrix t U α) i j) =
        (1 : Matrix (Fin r) (Fin r) K) i j :=
      congrArg (fun M : Matrix (Fin r) (Fin r) K => M i j)
        (formalFundamentalMatrix_constantCoeff (ordinaryPointClearedMatrix t U α))
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hij]
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [hw]
  simp

theorem universalOriginalEval_X_coeff_zero
    (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (α : K) (i : Fin r) :
    (universalOriginalEval q t U α (MvPolynomial.X i)).coeff 0 =
      q (MvPolynomial.X i) := by
  rw [universalOriginalEval_X_eq_ofPowerSeries]
  change (HahnSeries.ofPowerSeries ℤ H (universalPowerVector q t U α i)).coeff
    ((0 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    universalPowerVector_constantCoeff]

theorem universalOriginalEval_differential
    (q : MvPolynomial (Fin r) K →+* H)
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (P : MvPolynomial (Fin r) (RatFunc K)) :
    laurentOrdinaryAddDerivative (universalOriginalEval q t U α P) =
      universalOriginalEval q t U α
        (mvSystemD (rationalOrdinaryAddDerivative (K := K)) A P) := by
  change laurentOrdinaryAddDerivative
    (universalConstantEval q (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)
      (MvPolynomial.map (ordinaryPointRationalMap α) P))) =
    universalConstantEval q (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)
      (MvPolynomial.map (ordinaryPointRationalMap α)
        (mvSystemD (rationalOrdinaryAddDerivative (K := K)) A P)))
  rw [universalConstantEval_differential,
    matrixPolynomialSubst_differential (laurentOrdinaryAddDerivative (K := K))
      laurentOrdinaryAddDerivative_one laurentOrdinaryAddDerivative_mul
      (A.map (ordinaryPointRationalMap α)) (ordinaryPointLaurentFundamental t U α)
      (ordinaryPointLaurentFundamental_derivative A t U α hα hclear),
    mvSystemD_map (rationalOrdinaryAddDerivative (K := K))
      (laurentOrdinaryAddDerivative (K := K))
      rationalOrdinaryAddDerivative_one laurentOrdinaryAddDerivative_one
      rationalOrdinaryAddDerivative_mul laurentOrdinaryAddDerivative_mul
      (ordinaryPointRationalMap α) (ordinaryPointRationalMap_addDerivative α)]

theorem universalOriginalEval_iterate
    (q : MvPolynomial (Fin r) K →+* H)
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (P : MvPolynomial (Fin r) (RatFunc K)) (n : ℕ) :
    (laurentOrdinaryAddDerivative (K := H) : LaurentSeries H → LaurentSeries H)^[n]
      (universalOriginalEval q t U α P) =
    universalOriginalEval q t U α
      ((mvSystemD (rationalOrdinaryAddDerivative (K := K)) A :
        MvPolynomial (Fin r) (RatFunc K) → MvPolynomial (Fin r) (RatFunc K))^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      universalOriginalEval_differential q A t U α hα hclear]

theorem universalOriginalEval_system
    (q : MvPolynomial (Fin r) K →+* H)
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) (t : Polynomial K)
    (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j) (i : Fin r) :
    laurentOrdinaryAddDerivative (universalOriginalEval q t U α (MvPolynomial.X i)) =
      ∑ j, universalLaurentMap (q.comp MvPolynomial.C)
        (ordinaryPointRationalMap α (A i j)) *
        universalOriginalEval q t U α (MvPolynomial.X j) := by
  rw [universalOriginalEval_differential q A t U α hα hclear,
    mvSystemD_X _ rationalOrdinaryAddDerivative_one]
  simp only [matrixLinearForm, map_sum, map_mul, universalOriginalEval_C]

/-- The composed gauge evaluation is exactly ordinary multivariate evaluation
with the same translated rational coefficients and the constructed vector. -/
theorem universalOriginalEval_eq_eval₂Hom
    (q : MvPolynomial (Fin r) K →+* H)
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K) :
    universalOriginalEval q t U α =
      MvPolynomial.eval₂Hom
        ((universalLaurentMap (q.comp MvPolynomial.C)).comp (ordinaryPointRationalMap α))
        (fun i => universalOriginalEval q t U α (MvPolynomial.X i)) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    rw [universalOriginalEval_C, MvPolynomial.eval₂Hom_C]
    rfl
  · intro i
    rw [MvPolynomial.eval₂Hom_X']

end OriginalEvaluation

section OriginalRelations
variable {K : Type*} [Field K] [CharZero K] {r : ℕ}

theorem universalOriginalEval_kills_relation
    (t : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (α : K)
    (I : Ideal (MvPolynomial (Fin r) (RatFunc K)))
    (J0 : Ideal (MvPolynomial (Fin r) K)) [J0.IsPrime]
    [CharZero (universalConstantField J0)]
    (hdescent : J0.map (MvPolynomial.map (algebraMap K (LaurentSeries K))) =
      ordinaryPointGaugedIdeal t U α I)
    (P : MvPolynomial (Fin r) (RatFunc K)) (hP : P ∈ I) :
    universalOriginalEval (universalQuotientMap J0) t U α P = 0 := by
  have hP1 := Ideal.mem_map_of_mem (MvPolynomial.map (ordinaryPointRationalMap α)) hP
  have hP2 := Ideal.mem_map_of_mem
    (matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)).toRingHom hP1
  have hP3 : matrixPolynomialSubst (ordinaryPointLaurentFundamental t U α)
      (MvPolynomial.map (ordinaryPointRationalMap α) P) ∈
      J0.map (MvPolynomial.map (algebraMap K (LaurentSeries K))) := by
    rw [hdescent]
    exact hP2
  exact universalConstantEval_kills_extension J0 hP3

end OriginalRelations
end StrictEUnit
end
