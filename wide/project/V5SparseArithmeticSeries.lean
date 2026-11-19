import AnalyticFormalTaylor

noncomputable section
namespace StrictEUnit

def v5SparseCoefficients {k : Type*} [Zero k] (q : ℕ) (a : ℕ → k) : ℕ → k :=
  Function.extend (fun n : ℕ => q*n) a 0

theorem v5_mul_index_injective {q : ℕ} (hq : 0 < q) :
    Function.Injective (fun n : ℕ => q*n) := by
  intro n m h
  exact Nat.eq_of_mul_eq_mul_left hq h

theorem v5SparseCoefficients_at_multiple {k : Type*} [Zero k] {q : ℕ} (hq : 0 < q)
    (a : ℕ → k) (n : ℕ) : v5SparseCoefficients q a (q*n) = a n :=
  (v5_mul_index_injective hq).extend_apply a 0 n

theorem v5SparseCoefficients_off_range {k : Type*} [Zero k] (q : ℕ)
    (a : ℕ → k) (n : ℕ) (hn : n ∉ Set.range (fun m : ℕ => q*m)) :
    v5SparseCoefficients q a n = 0 :=
  Function.extend_apply' (f := fun m : ℕ => q*m) a (0 : ℕ → k) n hn

/-- Zero extension along n↦qn gives the actual power-substituted sum, keeping
all coefficients in the original ring. No topology on that ring is needed. -/
theorem v5_hasSum_sparse_power {k : Type*} [CommRing k] (ι : k →+* ℂ)
    {q : ℕ} (hq : 0 < q) (a : ℕ → k) (t z : ℂ)
    (ha : HasSum (fun n => ι (a n) * (t^q)^n) z) :
    HasSum (fun n => ι (v5SparseCoefficients q a n) * t^n) z := by
  have hs := (hasSum_extend_zero (v5_mul_index_injective hq)).mpr ha
  convert hs using 1
  funext n
  by_cases hn : n ∈ Set.range (fun m : ℕ => q*m)
  · obtain ⟨m, rfl⟩ := hn
    rw [v5SparseCoefficients_at_multiple hq,
      (v5_mul_index_injective hq).extend_apply]
    rw [pow_mul]
  · rw [v5SparseCoefficients_off_range q a n hn, map_zero, zero_mul,
      Function.extend_apply' _ _ _ hn]
    rfl

/-- Entire functions whose actual global sums have k-coefficients retain that
arithmetic coefficient description after the substitution t↦t^q. -/
theorem v5_entire_sparse_coefficient_recovery {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {q : ℕ} (hq : 0 < q) (a : ℕ → k)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ha : ∀ z : ℂ, HasSum (fun n => ι (a n) * z^n) (f z)) (n : ℕ) :
    entireCauchyCoefficient (fun t => f (t^q)) n = ι (v5SparseCoefficients q a n) := by
  apply entireCauchyCoefficient_eq_of_hasSum (hf.comp (differentiable_id.pow q))
  intro t
  exact v5_hasSum_sparse_power ι hq a t (f (t^q)) (ha (t^q))

/-- Exact formal coefficient-extension identity for the sparse k-series. -/
theorem v5_entire_sparse_formalTaylor {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {q : ℕ} (hq : 0 < q) (a : ℕ → k)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ha : ∀ z : ℂ, HasSum (fun n => ι (a n) * z^n) (f z)) :
    entireFormalTaylor (fun t => f (t^q)) =
      PowerSeries.map ι (PowerSeries.mk (v5SparseCoefficients q a)) := by
  ext n
  simp only [coeff_entireFormalTaylor, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact v5_entire_sparse_coefficient_recovery ι hq a f hf ha n

/-- Arithmetic coefficient membership is closed under positive power substitution,
for any coefficient homomorphism rather than only subfield inclusions. -/
theorem v5_entire_power_coefficients_in_range {k : Type*} [CommRing k]
    (ι : k →+* ℂ) {q : ℕ} (hq : 0 < q) (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (ha : ∀ n, entireCauchyCoefficient f n ∈ Set.range ι) :
    ∀ n, entireCauchyCoefficient (fun t => f (t^q)) n ∈ Set.range ι := by
  choose a ha using ha
  have hs (z : ℂ) : HasSum (fun n => ι (a n) * z^n) (f z) := by
    simpa only [ha] using entireCauchyCoefficient_hasSum hf z
  intro n
  exact ⟨v5SparseCoefficients q a n, (v5_entire_sparse_coefficient_recovery ι hq a f hf hs n).symm⟩

end StrictEUnit
#print axioms StrictEUnit.v5_hasSum_sparse_power
#print axioms StrictEUnit.v5_entire_sparse_coefficient_recovery

#print axioms StrictEUnit.v5_entire_sparse_formalTaylor
#print axioms StrictEUnit.v5_entire_power_coefficients_in_range
