import ActualFiniteLaurentArithmeticFrame
import SelectedScalarFieldMapTransport

noncomputable section
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

theorem powerSeries_unit_inverse_field_map (phi : K →+* L) (f : PowerSeries K)
    (hc : PowerSeries.constantCoeff K f≠0) :
    PowerSeries.map phi f⁻¹=(PowerSeries.map phi f)⁻¹ := by
  have hc' : PowerSeries.constantCoeff L (PowerSeries.map phi f)≠0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,PowerSeries.coeff_map] using (map_ne_zero phi).mpr hc
  apply (PowerSeries.eq_inv_iff_mul_eq_one hc').mpr
  rw [← map_mul,PowerSeries.inv_mul_cancel f hc,map_one]

theorem polynomialTailPowerSeries_field_map (phi : K →+* L) (d : ℕ) (P : Polynomial K) :
    PowerSeries.map phi (polynomialTailPowerSeries d P)=polynomialTailPowerSeries d (P.map phi) := by
  ext n
  simp only [polynomialTailPowerSeries,PowerSeries.coeff_map,PowerSeries.coeff_mk,Polynomial.coeff_map]

theorem sameCompanionEulerDenominatorSeries_field_map (phi : K →+* L) (T : Polynomial K) :
    PowerSeries.map phi (sameCompanionEulerDenominatorSeries T)=sameCompanionEulerDenominatorSeries (T.map phi) := by
  simp only [sameCompanionEulerDenominatorSeries,polynomialTailPowerSeries_field_map,polynomial_natTrailingDegree_map]

theorem sameCompanionEulerLastRowSeries_field_map (phi : K →+* L) (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) (j : Fin (n+1)) :
    PowerSeries.map phi (sameCompanionEulerLastRowSeries n T U j)=
      sameCompanionEulerLastRowSeries n (T.map phi) (fun i j =>(U i j).map phi) j := by
  simp only [sameCompanionEulerLastRowSeries,map_mul,
    powerSeries_unit_inverse_field_map phi _ (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT),
    sameCompanionEulerDenominatorSeries_field_map,sameCompanionEulerNumeratorSeries,
    polynomial_natTrailingDegree_map,polynomialTailPowerSeries_field_map,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]

theorem sameCompanionEulerPowerSeriesMatrix_field_map (phi : K →+* L) (n : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) :
    (sameCompanionEulerPowerSeriesMatrix n T U).map (PowerSeries.map phi)=
      sameCompanionEulerPowerSeriesMatrix n (T.map phi) (fun i j =>(U i j).map phi) := by
  funext i j
  cases i using Fin.lastCases with
  | last =>
    simp [sameCompanionEulerPowerSeriesMatrix,Matrix.diagonal_apply,
      sameCompanionEulerLastRowSeries_field_map phi n T U hT,PowerSeries.map_C]
    split_ifs <;> simp
  | cast i =>
    simp [sameCompanionEulerPowerSeriesMatrix,Matrix.diagonal_apply,
      Pi.single_apply,PowerSeries.map_C]
    split_ifs <;> simp

variable [CharZero K] [CharZero L]
theorem sourceLaurentEulerBase_field_map (phi : K →+* L) (n M : ℕ)
    (T : Polynomial K) (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) :
    (sourceLaurentEulerBase n T U M).map (PowerSeries.map phi)=
      sourceLaurentEulerBase n (T.map phi) (fun i j =>(U i j).map phi) M := by
  have he := sameCompanionEulerPowerSeriesMatrix_field_map phi n T U hT
  funext i j
  have hij := congrFun (congrFun he i) j
  simp only [sourceLaurentEulerBase,Matrix.map_apply,Matrix.add_apply,map_add,Matrix.diagonal_apply]
  change PowerSeries.map phi (sameCompanionEulerPowerSeriesMatrix n T U i j)=_ at hij
  rw [hij]
  split_ifs <;> simp [PowerSeries.map_C,polynomial_natTrailingDegree_map]

theorem augmentedSourceEulerColumn_field_map (phi : K →+* L) (n : ℕ)
    (T : Polynomial K) (hT : T≠0) (i : Fin (n+1)) :
    PowerSeries.map phi (augmentedSourceEulerColumn n T i)=augmentedSourceEulerColumn n (T.map phi) i := by
  simp only [augmentedSourceEulerColumn]
  split_ifs <;> simp only [map_zero,
    powerSeries_unit_inverse_field_map phi _ (sameCompanionEulerDenominatorSeries_constantCoeff_ne_zero T hT),
    sameCompanionEulerDenominatorSeries_field_map]

end StrictEUnit
end
