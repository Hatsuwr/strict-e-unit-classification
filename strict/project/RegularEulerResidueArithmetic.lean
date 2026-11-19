import RegularEulerFieldTransport
import RegularResidueIndicialRoots

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K]

@[simp] theorem powerSeriesEuler_constantCoeff (f : PowerSeries K) :
    PowerSeries.constantCoeff K (powerSeriesEuler f)=0 := by
  simp [powerSeriesEuler]

/-- The actual regular divided connection at zero is the residue's falling
matrix, with precisely the original factorial normalization. -/
theorem powerSeriesEulerFallingConnection_constantCoeff {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) :
    (powerSeriesEulerFallingConnection C m).map (PowerSeries.constantCoeff K)=
      matrixFallingProduct (C.map (PowerSeries.constantCoeff K)) m := by
  induction m with
  | zero =>funext i j;simp [powerSeriesEulerFallingConnection,matrixFallingProduct,Matrix.one_apply]
  | succ m ih =>
    funext i j
    have hi (a b) := congrFun (congrFun ih a) b
    simp only [Matrix.map_apply] at hi
    simp only [powerSeriesEulerFallingConnection,Matrix.map_apply,map_sub,map_add,map_sum,map_mul,
      map_natCast,powerSeriesEuler_constantCoeff,zero_add,hi,matrixFallingProduct,Matrix.mul_apply,
      Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,mul_sub,Finset.sum_sub_distrib]
    simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    ring

theorem powerSeriesEulerDividedConnection_constantCoeff {r : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (m : ℕ) (i j : Fin r) :
    PowerSeries.constantCoeff K (powerSeriesEulerDividedConnection C m i j)=
      matrixFallingProduct (C.map (PowerSeries.constantCoeff K)) m i j/(m.factorial : K) := by
  have h := congrFun (congrFun (powerSeriesEulerFallingConnection_constantCoeff C m) i) j
  simp only [Matrix.map_apply] at h
  simp only [powerSeriesEulerDividedConnection,map_mul,PowerSeries.constantCoeff_C,h,div_eq_mul_inv]
  ring

def MatrixBinomialPrefixArithmetic {r : ℕ} (M : Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ B : ℝ,1≤B ∧ ∀ N : ℕ,∃ D : ℕ,0<D ∧ (D : ℝ)≤B^(N+1) ∧
    ∀ m,m≤N →∀ i j,IsIntegral ℤ ((D : K)*(matrixFallingProduct M m i j/(m.factorial : K)))

/-- Restricting the SAME rectangular prefixes supplies residue arithmetic. -/
theorem RegularEulerPrefixArithmetic.residue {r : ℕ}
    {C : Matrix (Fin r) (Fin r) (PowerSeries K)} (hC : RegularEulerPrefixArithmetic C) :
    MatrixBinomialPrefixArithmetic (C.map (PowerSeries.constantCoeff K)) := by
  obtain ⟨B,hB,hden⟩ := hC
  refine ⟨B,hB,fun N =>?_⟩
  obtain ⟨D,hD,hDb,hDi⟩ := hden N
  refine ⟨D,hD,hDb,fun m hm i j =>?_⟩
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    powerSeriesEulerDividedConnection_constantCoeff] using hDi m hm 0 (Nat.zero_le N) i j

end StrictEUnit
end
