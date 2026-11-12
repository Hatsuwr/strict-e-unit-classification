import ScalarGaugeExponentArithmetic
import Mathlib.FieldTheory.SplittingField.Construction

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]

/-- The same monic scalar companion maps literally under field extension. -/
theorem monicScalarEulerCompanion_field_map {r : ℕ} (phi : K →+* L)
    (b : Fin (r+1) →PowerSeries K) (hb : b (Fin.last r)=1) :
    (scalarEulerPowerSeriesCompanion r b).map (PowerSeries.map phi)=
      scalarEulerPowerSeriesCompanion r (fun i =>PowerSeries.map phi (b i)) := by
  funext i j
  simp only [scalarEulerPowerSeriesCompanion,Matrix.map_apply,hb,map_one,inv_one,one_mul,
    apply_ite,map_zero,map_neg]
  split_ifs <;> rfl

/-- Exact field-map transport of the actual scalar coefficient symbols. -/
theorem scalarEulerCoefficientSymbol_field_map {r : ℕ} (phi : K →+* L)
    (b : Fin (r+1) →PowerSeries K) (k : ℕ) :
    (scalarEulerCoefficientSymbol r (fun i l =>PowerSeries.coeff K l (b i)) k).map phi=
      scalarEulerCoefficientSymbol r (fun i l =>PowerSeries.coeff L l (PowerSeries.map phi (b i))) k := by
  simp only [scalarEulerCoefficientSymbol,Polynomial.map_sum,Polynomial.map_monomial,PowerSeries.coeff_map]

/-- The already proved regular gauge, including its derivative, is retained
entrywise when extending coefficients. No new gauge arithmetic is assumed. -/
theorem monicScalarGauge_field_map {r : ℕ} (phi : K →+* L)
    (C G H : Matrix (Fin r) (Fin r) (PowerSeries K)) (b : Fin (r+1) →PowerSeries K)
    (hb : b (Fin.last r)=1) (hGH : G*H=1) (hHG : H*G=1)
    (hc : Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=scalarEulerPowerSeriesCompanion r b*G) :
    let f := PowerSeries.map phi
    G.map f*H.map f=1 ∧ H.map f*G.map f=1 ∧
      Matrix.of (fun i j =>powerSeriesEuler (G.map f i j))+G.map f*C.map f=
        scalarEulerPowerSeriesCompanion r (fun i =>f (b i))*G.map f := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · change (PowerSeries.map phi).mapMatrix G*(PowerSeries.map phi).mapMatrix H=1
    rw [← map_mul,hGH,map_one]
  · change (PowerSeries.map phi).mapMatrix H*(PowerSeries.map phi).mapMatrix G=1
    rw [← map_mul,hHG,map_one]
  · have hbmap := monicScalarEulerCompanion_field_map phi b hb
    funext i j
    have h := congrArg (PowerSeries.map phi) (congrFun (congrFun hc i) j)
    have hbentry (a b') := congrFun (congrFun hbmap a) b'
    simp only [Matrix.map_apply] at hbentry
    simpa only [Matrix.add_apply,Matrix.mul_apply,Matrix.of_apply,Matrix.map_apply,
      map_add,map_sum,map_mul,powerSeriesEuler_field_map,hbentry] using h

/-- The splitting field is finite, is a number field, and splits precisely the
mapped indicial polynomial of the ACTUAL monic tuple. -/
theorem scalarIndicial_finite_splitting_field [NumberField K] {r : ℕ}
    (b : Fin (r+1) →PowerSeries K) :
    let P := scalarEulerCoefficientSymbol r (fun i l =>PowerSeries.coeff K l (b i)) 0
    let L := P.SplittingField
    ∃ hNF : NumberField L,
      (scalarEulerCoefficientSymbol r
        (fun i l =>PowerSeries.coeff L l (PowerSeries.map (algebraMap K L) (b i))) 0).Splits (RingHom.id L) := by
  dsimp only
  let P := scalarEulerCoefficientSymbol r (fun i l =>PowerSeries.coeff K l (b i)) 0
  let L := P.SplittingField
  refine ⟨NumberField.of_module_finite K L,?_⟩
  rw [← scalarEulerCoefficientSymbol_field_map]
  apply (Polynomial.splits_map_iff (algebraMap K L) (RingHom.id L)).mpr
  simpa only [RingHom.id_comp] using Polynomial.SplittingField.splits P

end StrictEUnit
end
