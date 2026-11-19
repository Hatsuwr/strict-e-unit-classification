import NumberFieldPrimePlaceExistence

noncomputable section
namespace StrictEUnit
variable {K Γ₀ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ₀]

/-- An integral polynomial equation with no root modulo p supplies the
local translate-unit certificates at every p-place. -/
theorem polynomial_nonresidue_translate_unit_of_le_one (v : Valuation K Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : K) < 1)
    (a : K) (ha1 : v a ≤ 1) (P : Polynomial ℤ)
    (hroot : P.eval₂ (Int.castRingHom K) a = 0)
    (hnr : ∀ x : ZMod p, P.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    ∀ j : ℕ, v (a - (j : K)) = 1 := by
  let A : v.integer := ⟨a, ha1⟩
  let F : Polynomial v.integer := P.map (Int.castRingHom v.integer)
  intro j
  have hj := valuation_natCast_le_one v j
  apply le_antisymm (v.map_sub_le ha1 hj)
  by_contra h
  have hlt : v (a - (j : K)) < 1 := lt_of_not_ge h
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub A (j : v.integer) F
  have hcK := congrArg v.integer.subtype hc
  have heval (x : v.integer) : v.integer.subtype (F.eval x) =
      P.eval₂ (Int.castRingHom K) (x : K) := by
    have he : v.integer.subtype.comp (Int.castRingHom v.integer) = Int.castRingHom K := Subsingleton.elim _ _
    dsimp only [F]
    rw [Polynomial.eval_map, Polynomial.hom_eval₂, he]
    rfl
  have hid : -((P.eval (j : ℤ) : ℤ) : K) = (a - (j : K)) * (c : K) := by
    change v.integer.subtype (F.eval A) - v.integer.subtype (F.eval (j : v.integer)) =
      (a - (j : K)) * (c : K) at hcK
    rw [heval, heval] at hcK
    change P.eval₂ (Int.castRingHom K) a - P.eval₂ (Int.castRingHom K) (j : K) =
      (a - (j : K)) * (c : K) at hcK
    rw [hroot, zero_sub, Polynomial.eval₂_at_natCast] at hcK
    exact hcK
  have hc1 : v (c : K) ≤ 1 := c.property
  have hprod : v ((a - (j : K)) * (c : K)) < 1 := by
    rw [map_mul]
    exact (mul_le_mul_left' hc1 _).trans_lt (by simpa using hlt)
  have hnd : ¬ (p : ℤ) ∣ P.eval (j : ℤ) := by
    intro hd
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd (P.eval (j : ℤ)) p).mpr hd
    apply hnr (j : ZMod p)
    simpa only [Polynomial.eval₂_at_natCast] using hz
  rw [← hid, v.map_neg, valuation_intCast_unit_of_not_dvd v p hp hvp _ hnd] at hprod
  exact lt_irrefl _ hprod

/-- The global integral case discharges local boundedness automatically. -/
theorem polynomial_nonresidue_translate_unit (v : Valuation K Γ₀)
    (p : ℕ) (hp : p.Prime) (hvp : v (p : K) < 1)
    (a : K) (ha : IsIntegral ℤ a) (P : Polynomial ℤ)
    (hroot : P.eval₂ (Int.castRingHom K) a = 0)
    (hnr : ∀ x : ZMod p, P.eval₂ (Int.castRingHom (ZMod p)) x ≠ 0) :
    ∀ j : ℕ, v (a - (j : K)) = 1 :=
  polynomial_nonresidue_translate_unit_of_le_one v p hp hvp a
    (valuation_le_one_of_integer_integral v a ha) P hroot hnr

end StrictEUnit
end
