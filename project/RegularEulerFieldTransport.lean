import AugmentedSourceConstructedFrame

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit

/-- Rectangular common-prefix arithmetic of the actual regular Euler connection. -/
def RegularEulerPrefixArithmetic {K : Type*} [Field K] {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) : Prop :=
  ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
    ∀ m,m≤N →∀ l,l≤N →∀ i j,IsIntegral ℤ ((D : K)*PowerSeries.coeff K l
      (powerSeriesEulerDividedConnection C m i j))

variable {K L : Type*} [Field K] [Field L]

theorem powerSeriesDerivative_field_map (phi : K →+* L) (f : PowerSeries K) :
    PowerSeries.map phi (PowerSeries.derivative K f)=
      PowerSeries.derivative L (PowerSeries.map phi f) := by
  ext n
  simp only [PowerSeries.coeff_map,PowerSeries.coeff_derivative,map_mul,map_natCast,map_add,map_one]

theorem powerSeriesEuler_field_map (phi : K →+* L) (f : PowerSeries K) :
    PowerSeries.map phi (powerSeriesEuler f)=powerSeriesEuler (PowerSeries.map phi f) := by
  simp only [powerSeriesEuler,map_mul,PowerSeries.map_X,powerSeriesDerivative_field_map]

/-- Exact field-map transport, including every falling correction term. -/
theorem powerSeriesEulerFallingConnection_field_map {r : ℕ} (phi : K →+* L)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) :
    (powerSeriesEulerFallingConnection C m).map (PowerSeries.map phi)=
      powerSeriesEulerFallingConnection (C.map (PowerSeries.map phi)) m := by
  induction m with
  | zero =>funext i j;simp [powerSeriesEulerFallingConnection,Matrix.one_apply]
  | succ m ih =>
    funext i j
    have hi (a b) := congrFun (congrFun ih a) b
    simp only [Matrix.map_apply] at hi
    simp only [powerSeriesEulerFallingConnection,Matrix.map_apply,map_sub,map_add,map_sum,map_mul,
      map_natCast,powerSeriesEuler_field_map,hi]

theorem powerSeriesEulerDividedConnection_field_map {r : ℕ} (phi : K →+* L)
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) :
    (powerSeriesEulerDividedConnection C m).map (PowerSeries.map phi)=
      powerSeriesEulerDividedConnection (C.map (PowerSeries.map phi)) m := by
  funext i j
  have h := congrFun (congrFun (powerSeriesEulerFallingConnection_field_map phi C m) i) j
  simp only [Matrix.map_apply] at h
  simp only [powerSeriesEulerDividedConnection,Matrix.map_apply,map_mul,PowerSeries.map_C,
    map_inv₀,map_natCast,h]

/-- The same positive integers and exponential bound survive a field extension. -/
theorem RegularEulerPrefixArithmetic.field_map {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)}
    (hC : RegularEulerPrefixArithmetic C) (phi : K →+* L) :
    RegularEulerPrefixArithmetic (C.map (PowerSeries.map phi)) := by
  obtain ⟨B,hB,hden⟩ := hC
  refine ⟨B,hB,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,fun m hm l hl i j =>?_⟩
  have h := (hDi m hm l hl i j).map phi.toIntAlgHom
  have he := congrFun (congrFun (powerSeriesEulerDividedConnection_field_map phi C m) i) j
  rw [← he]
  simpa only [Matrix.map_apply,PowerSeries.coeff_map,RingHom.toIntAlgHom_apply,map_mul,map_natCast] using h

/-- Permuting the actual coordinates preserves the same connection prefixes. -/
theorem powerSeriesEulerFallingConnection_reindex {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (e : Equiv.Perm (Fin r)) (m : ℕ) :
    powerSeriesEulerFallingConnection (C.submatrix e e) m=
      (powerSeriesEulerFallingConnection C m).submatrix e e := by
  induction m with
  | zero =>funext i j;simp [powerSeriesEulerFallingConnection,Matrix.one_apply,Equiv.apply_eq_iff_eq]
  | succ m ih =>
    funext i j
    have hi (a b) := congrFun (congrFun ih a) b
    change ∀ a b,powerSeriesEulerFallingConnection (C.submatrix e e) m a b=
      powerSeriesEulerFallingConnection C m (e a) (e b) at hi
    simp only [powerSeriesEulerFallingConnection,hi,Matrix.submatrix_apply]
    rw [Equiv.sum_comp e (fun x =>powerSeriesEulerFallingConnection C m (e i) x*C x (e j))]

theorem RegularEulerPrefixArithmetic.reindex {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)} (hC : RegularEulerPrefixArithmetic C)
    (e : Equiv.Perm (Fin r)) : RegularEulerPrefixArithmetic (C.submatrix e e) := by
  obtain ⟨B,hB,hden⟩ := hC
  refine ⟨B,hB,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,fun m hm l hl i j =>?_⟩
  have he := congrFun (congrFun (powerSeriesEulerFallingConnection_reindex C e m) i) j
  change powerSeriesEulerFallingConnection (C.submatrix e e) m i j=
    powerSeriesEulerFallingConnection C m (e i) (e j) at he
  simpa only [powerSeriesEulerDividedConnection,he] using hDi m hm l hl (e i) (e j)

end StrictEUnit
end
