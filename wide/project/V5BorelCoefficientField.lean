import V5BorelSupportAssembly

noncomputable section
namespace StrictEUnit
open scoped BigOperators
variable {K : Type*} [Field K] [Algebra K ℂ]

def v5EulerPolynomialRowOver (j k : ℕ) : Polynomial K :=
  if k = j then Polynomial.X^j else 0

def v5BorelPolynomialRowOver {ι : Type*} [Fintype ι]
    (c : ι → K) (p j : ι → ℕ) (P k : ℕ) : Polynomial K :=
  ∑ i, Polynomial.C (c i) * v5TruncatePolynomialRow
    (v5IteratePolynomialRow (v5EulerPolynomialRowOver (K := K) (j i)) (j i) (P-p i))
    (j i+(P-p i)) k

theorem v5_map_truncatePolynomialRow (a : ℕ → Polynomial K) (m k : ℕ) :
    (v5TruncatePolynomialRow a m k).map (algebraMap K ℂ) =
      v5TruncatePolynomialRow (fun k => (a k).map (algebraMap K ℂ)) m k := by
  unfold v5TruncatePolynomialRow
  split <;> simp_all

theorem v5_map_iteratePolynomialRow (a : ℕ → Polynomial K) (m n k : ℕ) :
    (v5IteratePolynomialRow a m n k).map (algebraMap K ℂ) =
      v5IteratePolynomialRow (fun k => (a k).map (algebraMap K ℂ)) m n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [v5IteratePolynomialRow, v5DifferentiatePolynomialRow, Polynomial.map_add,
      ← Polynomial.derivative_map, v5_map_truncatePolynomialRow]
    have he : (fun k => (v5IteratePolynomialRow a m n k).map (algebraMap K ℂ)) =
        v5IteratePolynomialRow (fun k => (a k).map (algebraMap K ℂ)) m n := funext ih
    rw [he]
    cases k <;> simp [v5_map_truncatePolynomialRow, he]

theorem v5_map_borelPolynomialRowOver {ι : Type*} [Fintype ι]
    (c : ι → K) (p j : ι → ℕ) (P k : ℕ) :
    (v5BorelPolynomialRowOver c p j P k).map (algebraMap K ℂ) =
      v5BorelPolynomialRow (fun i => algebraMap K ℂ (c i)) p j P k := by
  have he (j : ℕ) : (fun k => (v5EulerPolynomialRowOver (K := K) j k).map (algebraMap K ℂ)) =
      v5EulerPolynomialRow j := by
    funext k
    by_cases h : k = j <;> simp [v5EulerPolynomialRowOver, v5EulerPolynomialRow, h]
  simp only [v5BorelPolynomialRowOver, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_C, v5_map_truncatePolynomialRow, v5_map_iteratePolynomialRow,
    he, v5BorelPolynomialRow]

theorem v5_natTrailingDegree_map (q : Polynomial K) :
    (q.map (algebraMap K ℂ)).natTrailingDegree = q.natTrailingDegree := by
  by_cases hq : q = 0
  · simp [hq]
  have hmap : q.map (algebraMap K ℂ) ≠ 0 := by
    exact (Polynomial.map_ne_zero_iff (algebraMap K ℂ).injective).mpr hq
  apply le_antisymm
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_map]
    exact (map_ne_zero (algebraMap K ℂ)).mpr (Polynomial.coeff_natTrailingDegree_ne_zero.mpr hq)
  · apply Polynomial.natTrailingDegree_le_of_ne_zero
    intro hzero
    have h := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hmap
    rw [Polynomial.coeff_map, hzero, map_zero] at h
    exact h rfl

/-- The Borel construction preserves the given coefficient field exactly.
Only the actual functions and formal Borel series are complex-valued. -/
theorem v5_borel_fuchs_ordinary_annihilator_over {m : ℕ} (hm : 0 < m)
    (q : Fin (m+1) → Polynomial K) (hlead : q ⟨m, by omega⟩ ≠ 0)
    (hval : ∀ i, q i ≠ 0 →
      (q ⟨m, by omega⟩).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m)
    (f : entireFunctionAlgebra) (B : PowerSeries ℂ)
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (hB : ∑ i, ((q i).map (algebraMap K ℂ) : PowerSeries ℂ) *
      (PowerSeries.derivative ℂ)^[i.val] B = 0) :
    ∃ (n : ℕ) (a : ℕ → Polynomial K), 0 < n ∧
      (∀ z, v5RowResidual f.val n a z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (a n).eval₂ (algebraMap K ℂ) z ≠ 0 := by
  classical
  let qc := fun i => (q i).map (algebraMap K ℂ)
  let last : Fin (m+1) := ⟨m, by omega⟩
  have hleadC : qc last ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K ℂ).injective).mpr hlead
  have hvalC : ∀ i, qc i ≠ 0 →
      (qc last).natTrailingDegree+i.val ≤ (qc i).natTrailingDegree+m := by
    intro i hi
    have hi' : q i ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K ℂ).injective).mp hi
    simpa only [qc, v5_natTrailingDegree_map] using hval i hi'
  let v := (qc last).natTrailingDegree
  let c (a : v5BorelSupport qc) := (q a.1).coeff a.2.val
  let cc (a : v5BorelSupport qc) := (qc a.1).coeff a.2.val
  have hcc : cc = fun i => algebraMap K ℂ (c i) := by funext i; exact Polynomial.coeff_map _ _
  let j (a : v5BorelSupport qc) := a.1.val
  let p (a : v5BorelSupport qc) := a.2.val+(m-a.1.val)-v
  let P := Finset.univ.sup p
  let a₀ : v5BorelSupport qc :=
    ⟨last, ⟨v, Polynomial.natTrailingDegree_mem_support_of_nonzero hleadC⟩⟩
  have hj : ∀ a, j a ≤ m := fun a => by have := a.1.isLt; dsimp [j]; omega
  have hp : ∀ a, p a ≤ P := fun a => Finset.le_sup (Finset.mem_univ a)
  have hj₀ : j a₀ = m := rfl
  have hp₀ : p a₀ = 0 := by simp [p, a₀, last]
  have hunique : ∀ a, a ≠ a₀ → j a < m ∨ 0 < p a := by
    intro a hne
    by_contra hn
    have ha := hj a
    have hja : j a = m := by omega
    have hpa : p a = 0 := by omega
    rcases a with ⟨i, s, hs⟩
    have hi : i = last := by apply Fin.ext; exact hja
    subst i
    have hsv : v ≤ s := Polynomial.natTrailingDegree_le_of_mem_supp s hs
    have hsp : s ≤ v := by simp only [p, last, Nat.sub_self, Nat.add_zero] at hpa; omega
    have he : s = v := by omega
    subst s
    exact hne rfl
  have hc : cc a₀ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hleadC
  have hshift := v5_borel_support_equation qc hvalC B hB
  have hann := v5_borelPolynomialRow_annihilates cc p j P m hj hp f B hBF hshift
  have hregular := fun z hz => v5_borelPolynomialRow_ordinary cc p j P m a₀
    hj hp hj₀ hp₀ hunique hc (z := z) hz
  let row := v5BorelPolynomialRowOver c p j P
  have hrow : ∀ k, (row k).map (algebraMap K ℂ) = v5BorelPolynomialRow cc p j P k := by
    intro k
    rw [hcc]
    exact v5_map_borelPolynomialRowOver c p j P k
  refine ⟨P+m, row, by omega, ?_, ?_⟩
  · intro z
    have he : v5RowResidual f.val (P+m) row z =
        v5RowResidual f.val (P+m) (v5BorelPolynomialRow cc p j P) z := by
      unfold v5RowResidual
      apply Finset.sum_congr rfl
      intro k _
      rw [← hrow k]
      change (row k).eval₂ (algebraMap K ℂ) z * _ =
        ((row k).map (algebraMap K ℂ)).eval z * _
      rw [Polynomial.eval_map]
    rw [he]
    exact hann z
  · intro z hz
    have h := hregular z hz
    rw [← hrow (P+m), Polynomial.eval_map] at h
    exact h

#print axioms v5_map_iteratePolynomialRow
#print axioms v5_map_borelPolynomialRowOver
#print axioms v5_natTrailingDegree_map
#print axioms v5_borel_fuchs_ordinary_annihilator_over
end StrictEUnit
end
