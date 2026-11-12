import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exterior power-exponential bounds for actual complex-valued functions.
The coordinate parameter permits both the full and punctured complex plane.
No analyticity, meromorphy, or analytic realization of the formal ring is
asserted. Those are separate inputs to the later analytic argument. -/
noncomputable section
namespace StrictEUnit
variable {Ω : Type*}

/-- The precise exterior bound, with a single positive constant controlling
both the leading coefficient and exponential rate. -/
def HasPowerExponentialBoundOn (N : ℕ) (z f : Ω → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, ∀ t, 1 ≤ ‖z t‖ →
    ‖f t‖ ≤ C * (1 + ‖z t‖) ^ M * Real.exp (C * ‖z t‖ ^ N)

/-- The full-plane specialization used for entire functions. -/
abbrev HasPowerExponentialBound (N : ℕ) (f : ℂ → ℂ) : Prop :=
  HasPowerExponentialBoundOn N id f

/-- Separate positive leading constant and nonnegative exponential rate can
be enlarged to the single constant in the manuscript's bound. -/
theorem powerExponentialBound_of_separate_constants (N M : ℕ) (z f : Ω → ℂ)
    (C E : ℝ) (hC : 0 < C) (hE : 0 ≤ E)
    (h : ∀ t, 1 ≤ ‖z t‖ →
      ‖f t‖ ≤ C * (1 + ‖z t‖) ^ M * Real.exp (E * ‖z t‖ ^ N)) :
    HasPowerExponentialBoundOn N z f := by
  refine ⟨C + E + 1, by linarith, M, fun t ht => (h t ht).trans ?_⟩
  have hp : 0 ≤ (1 + ‖z t‖) ^ M := pow_nonneg (by positivity) _
  have hn : 0 ≤ ‖z t‖ ^ N := pow_nonneg (norm_nonneg _) _
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right (by linarith) hp
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) hn)
  · exact (Real.exp_pos _).le
  · exact mul_nonneg (by linarith) hp

/-- Polynomial factors and exponential rates may both be enlarged. -/
theorem powerExponential_factor_mono {N M P : ℕ} {C D r : ℝ}
    (hr : 0 ≤ r) (hMP : M ≤ P) (hCD : C ≤ D) :
    (1 + r)^M * Real.exp (C * r^N) ≤
      (1 + r)^P * Real.exp (D * r^N) := by
  apply mul_le_mul
  · exact pow_le_pow_right₀ (by linarith) hMP
  · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCD (pow_nonneg hr _))
  · exact (Real.exp_pos _).le
  · exact pow_nonneg (by linarith) _

/-- Addition closure is proved for actual functions, with enlarged constants. -/
theorem powerExponentialBound_add (N : ℕ) (z f g : Ω → ℂ)
    (hf : HasPowerExponentialBoundOn N z f) (hg : HasPowerExponentialBoundOn N z g) :
    HasPowerExponentialBoundOn N z (f + g) := by
  obtain ⟨C, hC, M, hf⟩ := hf
  obtain ⟨D, hD, P, hg⟩ := hg
  apply powerExponentialBound_of_separate_constants N (M + P) z (f + g)
    (C + D) (C + D) (by linarith) (by linarith)
  intro t ht
  have hfm := mul_le_mul_of_nonneg_left
    (powerExponential_factor_mono (N := N) (M := M) (P := M+P)
      (norm_nonneg (z t)) (Nat.le_add_right _ _) (show C ≤ C+D by linarith)) hC.le
  have hgm := mul_le_mul_of_nonneg_left
    (powerExponential_factor_mono (N := N) (M := P) (P := M+P)
      (norm_nonneg (z t)) (Nat.le_add_left _ _) (show D ≤ C+D by linarith)) hD.le
  calc
    ‖(f + g) t‖ ≤ ‖f t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ C * ((1+‖z t‖)^(M+P) * Real.exp ((C+D)*‖z t‖^N)) +
        D * ((1+‖z t‖)^(M+P) * Real.exp ((C+D)*‖z t‖^N)) := by
      exact add_le_add ((hf t ht).trans (by simpa only [mul_assoc] using hfm))
        ((hg t ht).trans (by simpa only [mul_assoc] using hgm))
    _ = _ := by ring

/-- Multiplication closure uses the actual exponential addition law. -/
theorem powerExponentialBound_mul (N : ℕ) (z f g : Ω → ℂ)
    (hf : HasPowerExponentialBoundOn N z f) (hg : HasPowerExponentialBoundOn N z g) :
    HasPowerExponentialBoundOn N z (f * g) := by
  obtain ⟨C, hC, M, hf⟩ := hf
  obtain ⟨D, hD, P, hg⟩ := hg
  apply powerExponentialBound_of_separate_constants N (M+P) z (f*g)
    (C*D) (C+D) (mul_pos hC hD) (by linarith)
  intro t ht
  calc
    ‖(f*g) t‖ = ‖f t‖ * ‖g t‖ := norm_mul _ _
    _ ≤ (C * (1+‖z t‖)^M * Real.exp (C*‖z t‖^N)) *
        (D * (1+‖z t‖)^P * Real.exp (D*‖z t‖^N)) :=
      mul_le_mul (hf t ht) (hg t ht) (norm_nonneg _) (by positivity)
    _ = (C*D) * (1+‖z t‖)^(M+P) * Real.exp ((C+D)*‖z t‖^N) := by
      rw [add_mul, Real.exp_add, pow_add]
      ring

/-- Every constant function has the required bound. -/
theorem powerExponentialBound_const (N : ℕ) (z : Ω → ℂ) (c : ℂ) :
    HasPowerExponentialBoundOn N z (fun _ => c) := by
  apply powerExponentialBound_of_separate_constants N 0 z (fun _ => c)
    (‖c‖+1) 0 (by positivity) (by rfl)
  intro t ht
  simp only [pow_zero, mul_one, zero_mul, Real.exp_zero]
  linarith

/-- The actual function algebra's growth-bounded elements form a subalgebra.
This establishes closure of finite ring expressions, not arbitrary reciprocals. -/
def powerExponentialBoundSubalgebra (N : ℕ) (z : Ω → ℂ) : Subalgebra ℂ (Ω → ℂ) where
  carrier := {f | HasPowerExponentialBoundOn N z f}
  mul_mem' := fun hf hg => powerExponentialBound_mul N z _ _ hf hg
  add_mem' := fun hf hg => powerExponentialBound_add N z _ _ hf hg
  algebraMap_mem' c := powerExponentialBound_const N z c

/-- Bounds on generators imply bounds on every element of their actual
complex subalgebra, using the genuine Algebra.adjoin construction. -/
theorem powerExponentialBound_of_mem_adjoin (N : ℕ) (z : Ω → ℂ)
    (s : Set (Ω → ℂ)) (hs : ∀ f ∈ s, HasPowerExponentialBoundOn N z f)
    {f : Ω → ℂ} (hf : f ∈ Algebra.adjoin ℂ s) : HasPowerExponentialBoundOn N z f :=
  (Algebra.adjoin_le (show s ⊆ powerExponentialBoundSubalgebra N z from hs)) hf

end StrictEUnit
#print axioms StrictEUnit.HasPowerExponentialBoundOn
#print axioms StrictEUnit.HasPowerExponentialBound
#print axioms StrictEUnit.powerExponentialBound_of_separate_constants
#print axioms StrictEUnit.powerExponential_factor_mono
#print axioms StrictEUnit.powerExponentialBound_add
#print axioms StrictEUnit.powerExponentialBound_mul
#print axioms StrictEUnit.powerExponentialBound_const
#print axioms StrictEUnit.powerExponentialBoundSubalgebra
#print axioms StrictEUnit.powerExponentialBound_of_mem_adjoin
