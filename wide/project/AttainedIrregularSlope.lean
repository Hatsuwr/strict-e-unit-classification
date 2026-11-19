import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Finite numeric slope selection only. Zero polynomial indices are excluded
by the caller's finite set; no polynomial support or regularity is asserted. -/
namespace StrictEUnit

/-- An actual irregular index forces a maximum slope greater than one.
The selected natural weights satisfy all cross inequalities, with equality
at that same selected index. No coprimality is needed. -/
theorem exists_attained_irregular_slope
    (r t : ℕ) (hr : 0 < r) (ν : Fin r → ℕ) (S : Finset (Fin r))
    (hirregular : ∃ j ∈ S, ν j + (r-j.val) < t) :
    ∃ j0 ∈ S,
      let h := r-j0.val
      let a := t-ν j0
      0 < h ∧ h < a ∧ a ≤ h*t ∧
      (∀ i ∈ S, h*t ≤ h*ν i + a*(r-i.val)) ∧
      h*t = h*ν j0 + a*(r-j0.val) := by
  classical
  obtain ⟨j,hj,hbad⟩ := hirregular
  have hpos (i : Fin r) : 0 < r-i.val := by omega
  let slope : Fin r → ℚ := fun i => ((t-ν i : ℕ):ℚ) / ((r-i.val : ℕ):ℚ)
  obtain ⟨j0,hj0,hmax⟩ := S.exists_max_image slope ⟨j,hj⟩
  let h := r-j0.val
  let a := t-ν j0
  have hh : 0 < h := hpos j0
  have hjgap : r-j.val < t-ν j := by omega
  have hs : (1:ℚ) < slope j := by
    apply (lt_div_iff₀ (show (0:ℚ) < ((r-j.val : ℕ):ℚ) by exact_mod_cast hpos j)).2
    simpa only [one_mul] using (show (((r-j.val : ℕ):ℚ)) < ((t-ν j : ℕ):ℚ) by exact_mod_cast hjgap)
  have hs0 : (1:ℚ) < (a:ℚ)/(h:ℚ) := hs.trans_le (hmax j hj)
  have hha : h < a := by
    have he := (lt_div_iff₀ (show (0:ℚ) < (h:ℚ) by exact_mod_cast hh)).mp hs0
    simp only [one_mul] at he
    exact_mod_cast he
  have hν : ν j0 ≤ t := by dsimp [a] at hha; omega
  have hat : a ≤ t := Nat.sub_le _ _
  have htht : t ≤ h*t := by
    calc
      t = 1*t := (one_mul t).symm
      _ ≤ h*t := Nat.mul_le_mul_right t hh
  have hcross (i : Fin r) (hi : i ∈ S) : h*(t-ν i) ≤ a*(r-i.val) := by
    have he := (div_le_div_iff₀
      (show (0:ℚ) < ((r-i.val : ℕ):ℚ) by exact_mod_cast hpos i)
      (show (0:ℚ) < (h:ℚ) by exact_mod_cast hh)).mp (hmax i hi)
    have he' : (t-ν i)*h ≤ a*(r-i.val) := by exact_mod_cast he
    simpa only [Nat.mul_comm (t-ν i) h] using he'
  refine ⟨j0,hj0,hh,hha,hat.trans htht,?_,?_⟩
  · intro i hi
    have ht : t ≤ ν i + (t-ν i) := by omega
    calc
      h*t ≤ h*(ν i+(t-ν i)) := Nat.mul_le_mul_left h ht
      _ = h*ν i+h*(t-ν i) := Nat.mul_add _ _ _
      _ ≤ h*ν i+a*(r-i.val) := Nat.add_le_add_left (hcross i hi) _
  · have he : t = ν j0+a := by dsimp [a]; omega
    change h*t = h*ν j0+a*h
    rw [he, Nat.mul_add, Nat.mul_comm h a]

end StrictEUnit
