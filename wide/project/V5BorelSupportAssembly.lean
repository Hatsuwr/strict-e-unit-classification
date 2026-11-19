import V5BorelOrdinaryAction
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

namespace StrictEUnit
open scoped BigOperators

abbrev v5BorelSupport {m : ℕ} (q : Fin (m+1) → Polynomial ℂ) :=
  Σ i : Fin (m+1), {s : ℕ // s ∈ (q i).support}

/-- Multiplying the original polynomial Borel equation and cancelling its
common power of X gives the shifted finite support equation. -/
theorem v5_borel_support_equation {m v : ℕ} (q : Fin (m+1) → Polynomial ℂ)
    (hval : ∀ i, q i ≠ 0 → v+i.val ≤ (q i).natTrailingDegree+m)
    (B : PowerSeries ℂ)
    (hB : ∑ i, (q i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] B = 0) :
    (∑ a : v5BorelSupport q, PowerSeries.C ℂ ((q a.1).coeff a.2.val) *
      (PowerSeries.X^(a.2.val+(m-a.1.val)-v) * v5EulerFalling a.1.val B)) = 0 := by
  classical
  have hnonzero : (PowerSeries.X : PowerSeries ℂ)^v ≠ 0 :=
    pow_ne_zero v PowerSeries.X_ne_zero
  apply (mul_left_cancel₀ hnonzero)
  rw [mul_zero, Finset.mul_sum, Fintype.sum_sigma]
  have hterm (i : Fin (m+1)) (s : {s : ℕ // s ∈ (q i).support}) :
      (PowerSeries.X : PowerSeries ℂ)^v *
        (PowerSeries.C ℂ ((q i).coeff s.val) *
          (PowerSeries.X^(s.val+(m-i.val)-v) * v5EulerFalling i.val B)) =
      PowerSeries.X^m * (PowerSeries.C ℂ ((q i).coeff s.val) *
        PowerSeries.X^s.val * (PowerSeries.derivative ℂ)^[i.val] B) := by
    have hq : q i ≠ 0 := by
      intro hz
      simpa [hz] using s.property
    have hs := Polynomial.natTrailingDegree_le_of_mem_supp s.val s.property
    have hv := hval i hq
    have hi := i.isLt
    have he : v+(s.val+(m-i.val)-v)+i.val = m+s.val := by omega
    unfold v5EulerFalling
    calc
      _ = PowerSeries.C ℂ ((q i).coeff s.val) *
          (PowerSeries.X^v * PowerSeries.X^(s.val+(m-i.val)-v) * PowerSeries.X^i.val) *
          (PowerSeries.derivative ℂ)^[i.val] B := by ring
      _ = _ := by
        rw [← pow_add, ← pow_add, he, pow_add]
        ring
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  have hpoly (i : Fin (m+1)) :
      (∑ s : {s : ℕ // s ∈ (q i).support},
        PowerSeries.C ℂ ((q i).coeff s.val) * PowerSeries.X^s.val *
          (PowerSeries.derivative ℂ)^[i.val] B) =
      (q i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] B := by
    rw [← Finset.sum_mul]
    change (∑ s ∈ (q i).support.attach, PowerSeries.C ℂ ((q i).coeff s.val) *
      PowerSeries.X^s.val) * _ = _
    rw [Finset.sum_attach (q i).support (fun s : ℕ => PowerSeries.C ℂ ((q i).coeff s) * PowerSeries.X^s)]
    congr 1
    simpa only [map_sum, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X] using
      congrArg (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ)
        (q i).as_sum_support_C_mul_X_pow.symm
  simp_rw [hpoly]
  rw [hB, mul_zero]

/-- A positive-order polynomial Borel equation Fuchsian at zero supplies an
actual entire annihilator ordinary at every nonzero point. -/
theorem v5_borel_fuchs_ordinary_annihilator {m : ℕ} (hm : 0 < m)
    (q : Fin (m+1) → Polynomial ℂ) (hlead : q ⟨m, by omega⟩ ≠ 0)
    (hval : ∀ i, q i ≠ 0 →
      (q ⟨m, by omega⟩).natTrailingDegree+i.val ≤ (q i).natTrailingDegree+m)
    (f : entireFunctionAlgebra) (B : PowerSeries ℂ)
    (hBF : ∀ n, PowerSeries.coeff ℂ n B = v5FactorialCoeff (entireTaylorAlgHom f) n)
    (hB : ∑ i, (q i : PowerSeries ℂ) * (PowerSeries.derivative ℂ)^[i.val] B = 0) :
    ∃ (n : ℕ) (a : ℕ → Polynomial ℂ), 0 < n ∧
      (∀ z, v5RowResidual f.val n a z = 0) ∧
      ∀ z : ℂ, z ≠ 0 → (a n).eval z ≠ 0 := by
  classical
  let last : Fin (m+1) := ⟨m, by omega⟩
  let v := (q last).natTrailingDegree
  let c (a : v5BorelSupport q) := (q a.1).coeff a.2.val
  let j (a : v5BorelSupport q) := a.1.val
  let p (a : v5BorelSupport q) := a.2.val+(m-a.1.val)-v
  let P := Finset.univ.sup p
  let a₀ : v5BorelSupport q :=
    ⟨last, ⟨v, Polynomial.natTrailingDegree_mem_support_of_nonzero hlead⟩⟩
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
  have hc : c a₀ ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hlead
  apply v5_borel_ordinary_annihilator c p j P m a₀ hj hp hj₀ hp₀ hunique hc
    (by omega) f B hBF
  exact v5_borel_support_equation q hval B hB

#print axioms v5_borel_support_equation
#print axioms v5_borel_fuchs_ordinary_annihilator
end StrictEUnit
