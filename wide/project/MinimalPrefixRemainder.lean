import OrdinaryBorelMinimalCyclic

/-! Source-only nonvanishing bridge. Only the independent prefix is used.
No cyclic-row, determinant, contact or arithmetic estimate is asserted. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit

/-- A genuinely nonzero polynomial row cannot annihilate a rationally independent
Laurent family. The polynomial action is the exact canonical multiplication. -/
theorem polynomial_row_remainder_ne_zero {K : Type*} [Field K] {r : ℕ}
    (Y : Fin r → LaurentSeries K) (hY : LinearIndependent (RatFunc K) Y)
    (P : Fin r → Polynomial K) (hP : ∃ i, P i ≠ 0) :
    (∑ i, algebraMap (Polynomial K) (LaurentSeries K) (P i) * Y i) ≠ 0 := by
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  intro hz
  have hsum : ∑ i, algebraMap (Polynomial K) (RatFunc K) (P i) • Y i = 0 := by
    calc
      _ = ∑ i, algebraMap (Polynomial K) (LaurentSeries K) (P i) * Y i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply
          (Polynomial K) (RatFunc K) (LaurentSeries K)]
      _ = 0 := hz
  obtain ⟨i, hi⟩ := hP
  have hzero := (Fintype.linearIndependent_iff.1 hY)
    (fun j => algebraMap (Polynomial K) (RatFunc K) (P j)) hsum i
  apply hi
  apply RatFunc.algebraMap_injective K
  simpa only [map_zero] using hzero

/-- Apply nonvanishing to precisely the original minimal derivative prefix.
Neither the unit channel nor the already dependent derivative of order r is added. -/
theorem minimal_prefix_polynomial_remainder_ne_zero {K : Type*} [Field K]
    (G : LaurentSeries K) (r : ℕ) (b : Fin r → RatFunc K)
    (hdata : OrdinaryBorelMinimalCyclicData G r b)
    (P : Fin r → Polynomial K) (hP : ∃ i, P i ≠ 0) :
    (∑ i, algebraMap (Polynomial K) (LaurentSeries K) (P i) *
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G) ≠ 0 := by
  exact polynomial_row_remainder_ne_zero
    (fun i : Fin r =>
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] G)
    hdata.1 P hP

end StrictEUnit
end
