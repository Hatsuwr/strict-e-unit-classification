import MinimalDifferentialCompanion

/-! Unscaled covariant rows for a genuine differential scalar field.
No scalar-field linearity of the ambient derivation, row cyclicity, rank,
contact or arithmetic denominator estimate is assumed or concluded. -/
noncomputable section
open scoped BigOperators Classical
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- The unscaled rational covariant row operator q ↦ dB(q) + q A. -/
def rationalCovariantRow {r : ℕ} (dB : Derivation k B B)
    (A : Fin r → Fin r → B) (q : Fin r → B) : Fin r → B :=
  fun j => dB (q j) + ∑ i, q i * A i j

/-- Exact Leibniz rule for evaluation of a row on the SAME system solution. -/
theorem rationalCovariantRow_eval {r : ℕ}
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (A : Fin r → Fin r → B) (Y : Fin r → R)
    (hY : ∀ i, d (Y i) = ∑ j, A i j • Y j) (q : Fin r → B) :
    d (∑ i, q i • Y i) = ∑ j, rationalCovariantRow dB A q j • Y j := by
  have hsmul (b : B) (x : R) :
      d (b • x) = dB b • x + b • d x := by
    simp only [Algebra.smul_def, d.leibniz, hcompat, smul_eq_mul,
      Algebra.id.map_eq_self, mul_comm, add_comm]
  calc
    d (∑ i, q i • Y i) =
        (∑ i, dB (q i) • Y i) + ∑ i, ∑ j, (q i * A i j) • Y j := by
      rw [map_sum]
      simp only [hsmul, hY, Finset.smul_sum, ← mul_smul, Finset.sum_add_distrib]
    _ = (∑ j, dB (q j) • Y j) + ∑ j, ∑ i, (q i * A i j) • Y j := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ j, rationalCovariantRow dB A q j • Y j := by
      simp only [rationalCovariantRow, add_smul, Finset.sum_smul,
        Finset.sum_add_distrib]

/-- Iteration uses the unscaled covariant operator itself, not a false cleared T^n formula. -/
theorem rationalCovariantRow_iterate_eval {r : ℕ}
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (A : Fin r → Fin r → B) (Y : Fin r → R)
    (hY : ∀ i, d (Y i) = ∑ j, A i j • Y j) (q : Fin r → B) (n : ℕ) :
    ((d : R → R)^[n]) (∑ i, q i • Y i) =
      ∑ j, ((rationalCovariantRow dB A)^[n]) q j • Y j := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        rationalCovariantRow_eval dB d hcompat A Y hY,
        Function.iterate_succ_apply']

/-- Specialization to the exact normalized companion of an initial derivative prefix.
The recurrence is the only additional premise; no assertion of cyclicity for q is made. -/
theorem minimalDerivativeCompanion_covariant_iterate
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (f : R) (r : ℕ) (b q : Fin r → B)
    (hrec : ∑ j, b j • ((d : R → R)^[j.val]) f = ((d : R → R)^[r]) f)
    (n : ℕ) :
    ((d : R → R)^[n]) (∑ i, q i • ((d : R → R)^[i.val]) f) =
      ∑ j, ((rationalCovariantRow dB (minimalDerivativeCompanion r b))^[n]) q j •
        ((d : R → R)^[j.val]) f := by
  exact rationalCovariantRow_iterate_eval dB d hcompat
    (minimalDerivativeCompanion r b) (fun i => ((d : R → R)^[i.val]) f)
    (minimalDerivativeCompanion_rows d f r b hrec) q n

end StrictEUnit
end
