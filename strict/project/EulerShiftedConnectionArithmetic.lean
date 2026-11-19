import EulerShiftedConnectionOperator

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

theorem powerSeriesEuler_map (phi : K →+* L) (f : PowerSeries K) :
    PowerSeries.map phi (powerSeriesEuler f)=powerSeriesEuler (PowerSeries.map phi f) := by
  have hd : PowerSeries.map phi (PowerSeries.derivative K f)=
      PowerSeries.derivative L (PowerSeries.map phi f) := by
    ext n
    simp only [PowerSeries.coeff_map,PowerSeries.coeff_derivative,map_mul,map_natCast,map_add,map_one]
  simp only [powerSeriesEuler,map_mul,PowerSeries.map_X,hd]

theorem powerSeriesEulerFallingConnection_map (phi : K →+* L) {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i j : Fin r) :
    PowerSeries.map phi (powerSeriesEulerFallingConnection C m i j)=
      powerSeriesEulerFallingConnection (C.map (PowerSeries.map phi)) m i j := by
  classical
  induction m generalizing i j with
  | zero =>
    simp only [powerSeriesEulerFallingConnection,Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    simp only [powerSeriesEulerFallingConnection,map_sub,map_add,map_sum,map_mul,map_natCast,
      powerSeriesEuler_map,ih,Matrix.map_apply]

theorem powerSeriesEulerDividedConnection_map (phi : K →+* L) {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i j : Fin r) :
    PowerSeries.map phi (powerSeriesEulerDividedConnection C m i j)=
      powerSeriesEulerDividedConnection (C.map (PowerSeries.map phi)) m i j := by
  simp only [powerSeriesEulerDividedConnection,map_mul,PowerSeries.map_C,map_inv₀,map_natCast,
    powerSeriesEulerFallingConnection_map]

theorem powerSeriesEulerDividedConnection_denominators_map (phi : K →+* L) {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j))) :
    ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : L)*
        PowerSeries.coeff L l (powerSeriesEulerDividedConnection (C.map (PowerSeries.map phi)) m i j)) := by
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,?_⟩
  intro m hm l hl i j
  have h := (hDi m hm l hl i j).map phi.toIntAlgHom
  rw [← powerSeriesEulerDividedConnection_map,PowerSeries.coeff_map]
  simpa only [RingHom.toIntAlgHom_apply,map_mul,map_natCast] using h

/-- Exact exponent-shifted connection arithmetic for a WHOLE family. The
product of two already-derived prefix denominators suffices. -/
theorem powerSeriesEulerShiftedDividedConnection_denominators [CharZero K] {r : ℕ} {ι : Type*}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (B : ℝ) (hB : 1≤B)
    (hden : ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerDividedConnection C m i j)))
    (rho : ι → K) (hrho : JointBinomialPrefixDenominators rho) :
    ∃ E : ℝ,1≤E ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤E^(N+1) ∧
      ∀ m,m≤N → ∀ l,l≤N → ∀ i j u,IsIntegral ℤ ((D : K)*
        PowerSeries.coeff K l (powerSeriesEulerShiftedDividedConnection C (rho u) m i j)) := by
  obtain ⟨H,hH,hneg⟩ := jointBinomialPrefixDenominators_neg rho hrho
  refine ⟨B*H,one_le_mul_of_one_le_of_one_le hB hH,?_⟩
  intro N
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  obtain ⟨e,he,heb,hei⟩ := hneg N
  refine ⟨D*e,Nat.mul_pos hD he,?_,?_⟩
  · rw [Nat.cast_mul,mul_pow]
    exact mul_le_mul hDb heb (Nat.cast_nonneg e) (pow_nonneg (le_trans zero_le_one hB) _)
  · intro m hm l hl i j u
    simp only [powerSeriesEulerShiftedDividedConnection,map_sum,PowerSeries.coeff_C_mul,Finset.mul_sum]
    apply IsIntegral.sum
    rintro ⟨a,b⟩ hab
    have hab' := Finset.mem_antidiagonal.mp hab
    have hb := hDi b (by omega) l hl i j
    have ha := hei a (by omega) u
    rw [← field_choose_eq_descPochhammer_div] at ha
    convert ha.mul hb using 1
    push_cast
    ring

end StrictEUnit
end
