import FourierLaurentRealization

/-! A fixed, finite all-integer resonance index and the full Laurent solution
space. The solution space is the kernel of the actual operator, not a span. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {K : Type*} [Field K]

def powerSeriesCoefficientEmbedding :
    (ℕ → Polynomial K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun u := ((PowerSeries.mk u : PowerSeries (Polynomial K)) : LaurentSeries (Polynomial K))
  map_add' u v := by
    apply HahnSeries.ext
    funext n
    simp only [PowerSeries.coeff_coe,HahnSeries.coeff_add]
    split_ifs <;> simp only [PowerSeries.coeff_mk,Pi.add_apply,add_zero]
  map_smul' c u := by
    apply HahnSeries.ext
    funext n
    simp only [PowerSeries.coeff_coe,HahnSeries.coeff_smul]
    split_ifs <;> simp only [PowerSeries.coeff_mk,Pi.smul_apply,smul_zero,RingHom.id_apply]

def laurentCoefficientShiftLinear (k : ℤ) :
    LaurentSeries (Polynomial K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun := laurentCoefficientShift k
  map_add' s t := by
    apply HahnSeries.ext
    funext n
    simp only [laurentCoefficientShift_coeff,HahnSeries.coeff_add]
  map_smul' c s := by
    apply HahnSeries.ext
    funext n
    simp only [laurentCoefficientShift_coeff,HahnSeries.coeff_smul,RingHom.id_apply]

def twistedPolynomialCoefficientEulerLinear (ξ : K) :
    LaurentSeries (Polynomial K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun := twistedPolynomialCoefficientEuler ξ
  map_add' s t := by
    apply HahnSeries.ext
    funext n
    simp only [twistedPolynomialCoefficientEuler_coeff,HahnSeries.coeff_add,map_add]
  map_smul' c s := by
    apply HahnSeries.ext
    funext n
    simp only [twistedPolynomialCoefficientEuler_coeff,HahnSeries.coeff_smul,map_smul,
      RingHom.id_apply]

theorem laurentCoefficient_smul_eq_mul (c : K) (s : LaurentSeries (Polynomial K)) :
    c • s = HahnSeries.single 0 (Polynomial.C c) * s := by
  apply HahnSeries.ext
  funext n
  rw [HahnSeries.coeff_smul,HahnSeries.coeff_single_zero_mul,Polynomial.smul_eq_C_mul]

def scalarTwistedCoefficientLinear (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) :
    LaurentSeries (Polynomial K) →ₗ[K] LaurentSeries (Polynomial K) where
  toFun := scalarTwistedCoefficientOperator r b ξ
  map_add' s t := by
    have h (i : ℕ) : (twistedPolynomialCoefficientEuler ξ)^[i] (s+t) =
        (twistedPolynomialCoefficientEuler ξ)^[i] s +
          (twistedPolynomialCoefficientEuler ξ)^[i] t := by
      exact iterate_map_add (twistedPolynomialCoefficientEulerLinear ξ) i s t
    simp only [scalarTwistedCoefficientOperator,h,mul_add,Finset.sum_add_distrib]
  map_smul' c s := by
    have h (i : ℕ) : (twistedPolynomialCoefficientEuler ξ)^[i] (c • s) =
        c • (twistedPolynomialCoefficientEuler ξ)^[i] s := by
      induction i with
      | zero => rfl
      | succ i ih =>
        rw [Function.iterate_succ_apply',ih,Function.iterate_succ_apply']
        exact (twistedPolynomialCoefficientEulerLinear ξ).map_smul c _
    simp only [scalarTwistedCoefficientOperator,h,Finset.smul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [laurentCoefficient_smul_eq_mul]
    ring

/-- ALL actual Laurent coefficient solutions of the literal operator. -/
def polynomialLogLaurentSolutionSpace (r : ℕ) (b : Fin (r+1) → PowerSeries K) (ξ : K) :
    Submodule K (LaurentSeries (Polynomial K)) :=
  LinearMap.ker (scalarTwistedCoefficientLinear r b ξ)

variable [CharZero K]

def polynomialIntegerResonanceIndices (ξ : K) (P : Polynomial K) : Finset ℤ :=
  P.roots.toFinset.preimage (fun k : ℤ => ξ + (k : K))
    (show Function.Injective (fun k : ℤ => ξ + (k : K)) from
      fun k l h => Int.cast_injective (add_left_cancel h)).injOn

@[simp] theorem polynomialIntegerResonanceIndices_mem (ξ : K) (P : Polynomial K) (k : ℤ) :
    k ∈ polynomialIntegerResonanceIndices ξ P ↔ P.rootMultiplicity (ξ+(k : K)) ≠ 0 := by
  simp only [polynomialIntegerResonanceIndices,Finset.mem_preimage,Multiset.mem_toFinset,
    ← Multiset.count_pos,Polynomial.count_roots,Nat.pos_iff_ne_zero]

def polynomialLogIntegerResonanceIndex (ξ : K) (P : Polynomial K) :=
  Σ k : {k : ℤ // k ∈ polynomialIntegerResonanceIndices ξ P},
    Fin (P.rootMultiplicity (ξ+(k.1 : K)))

instance polynomialLogIntegerResonanceIndexFintype (ξ : K) (P : Polynomial K) :
    Fintype (polynomialLogIntegerResonanceIndex ξ P) := by
  unfold polynomialLogIntegerResonanceIndex
  infer_instance

def polynomialIntegerResonanceCost (ξ : K) (P : Polynomial K) : ℕ :=
  ∑ k ∈ polynomialIntegerResonanceIndices ξ P,P.rootMultiplicity (ξ+(k : K))

theorem polynomialLogIntegerResonanceIndex_card (ξ : K) (P : Polynomial K) :
    Fintype.card (polynomialLogIntegerResonanceIndex ξ P) =
      polynomialIntegerResonanceCost ξ P := by
  simp only [polynomialLogIntegerResonanceIndex,Fintype.card_sigma,Fintype.card_fin]
  exact Finset.sum_coe_sort (polynomialIntegerResonanceIndices ξ P)
    (fun k => P.rootMultiplicity (ξ+(k : K)))

theorem polynomialIntegerResonanceCost_le (ξ : K) (P : Polynomial K) :
    polynomialIntegerResonanceCost ξ P ≤ P.natDegree :=
  polynomial_rootMultiplicity_sum_injective_le P _ _
    (by intro k l h; exact Int.cast_injective (add_left_cancel h))

def integerResonanceFrobeniusCoefficients (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogIntegerResonanceIndex ξ (B 0)) : LaurentSeries (Polynomial K) :=
  laurentCoefficientShift i.1.1 (powerSeriesCoefficientEmbedding
    (polynomialLogFrobeniusCoefficient B (ξ+(i.1.1 : K)) (Polynomial.X^i.2.1)))

def integerResonanceFrobeniusAmplitude (B : ℕ → Polynomial K) (ξ : K)
    (i : polynomialLogIntegerResonanceIndex ξ (B 0)) : Polynomial (LaurentSeries K) :=
  frobeniusIntegerShift i.1.1
    (polynomialLogFrobeniusAmplitude B (ξ+(i.1.1 : K)) (Polynomial.X^i.2.1))

theorem integerResonanceFrobeniusAmplitude_representation
    (B : ℕ → Polynomial K) (ξ : K) (i : polynomialLogIntegerResonanceIndex ξ (B 0)) :
    logPolynomialToCoefficientSeries (integerResonanceFrobeniusAmplitude B ξ i) =
      integerResonanceFrobeniusCoefficients B ξ i := by
  unfold integerResonanceFrobeniusAmplitude integerResonanceFrobeniusCoefficients
  rw [logPolynomialToCoefficientSeries_integerShift]
  congr 1
  exact logPolynomialToCoefficientSeries_transpose_powerSeries_mk _ _
    (polynomialLogFrobeniusCoefficient_coeff_eq_zero _ _ _)

end StrictEUnit
end

#print axioms StrictEUnit.polynomialIntegerResonanceIndices_mem
#print axioms StrictEUnit.polynomialLogIntegerResonanceIndex_card
#print axioms StrictEUnit.polynomialIntegerResonanceCost_le
#print axioms StrictEUnit.integerResonanceFrobeniusAmplitude_representation
