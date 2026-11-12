import IdealNormPrimeLowerBound
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.FieldTheory.Finiteness

noncomputable section
open scoped NumberField nonZeroDivisors BigOperators
open NumberField
namespace StrictEUnit

/-- Degree-one residue extensions have ideal norm exactly the underlying prime. -/
theorem absNorm_eq_prime_of_inertia_one
    (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (P : Ideal (𝓞 K))
    [hmax : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal]
    [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (hf : Ideal.inertiaDeg (Ideal.span ({(p : ℤ)} : Set ℤ)) P = 1) :
    Ideal.absNorm P = p := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  letI : q.IsMaximal := hmax
  letI : Field (ℤ ⧸ q) := Ideal.Quotient.field q
  have hd : Module.finrank (ℤ ⧸ q) ((𝓞 K) ⧸ P) = 1 :=
    (Ideal.inertiaDeg_algebraMap q P).symm.trans hf
  letI : Module.Finite (ℤ ⧸ q) ((𝓞 K) ⧸ P) := Module.finite_of_finrank_pos (by omega)
  change Nat.card ((𝓞 K) ⧸ P) = p
  rw [Module.natCard_eq_pow_finrank (K := ℤ ⧸ q), hd, pow_one]
  exact (Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv).trans (Nat.card_zmod p)

/-- For a Galois number field, the exact e=f=1 criterion supplies the
full-degree family of distinct norm-p ideals. No prime existence is asserted. -/
theorem galois_split_prime_norm_certificate
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) (hp : p.Prime)
    (he : Ideal.ramificationIdxIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1)
    (hf : Ideal.inertiaDegIn (Ideal.span ({(p : ℤ)} : Set ℤ)) (𝓞 K) = 1) :
    ∃ P : Fin (Module.finrank ℚ K) → (Ideal (𝓞 K))⁰,
      Function.Injective P ∧ ∀ i, Ideal.absNorm (P i : Ideal (𝓞 K)) = p := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hq0 : q ≠ ⊥ := by simpa [q, Ideal.span_singleton_eq_bot] using hp.ne_zero
  letI : q.IsPrime := (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)
  letI : q.IsMaximal := (inferInstance : q.IsPrime).isMaximal hq0
  have hc := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hq0 (𝓞 K) ℚ K
  change (Ideal.primesOver q (𝓞 K)).ncard * (_ * _) = _ at hc
  rw [he, hf, mul_one, mul_one] at hc
  letI := (primesOver_finite q (𝓞 K)).to_subtype
  letI := Fintype.ofFinite (Ideal.primesOver q (𝓞 K))
  have hcard : Fintype.card (Ideal.primesOver q (𝓞 K)) = Module.finrank ℚ K := by
    rw [← Nat.card_eq_fintype_card, Set.Nat.card_coe_set_eq]
    exact hc
  let e := (Fintype.equivFinOfCardEq hcard).symm
  have hnonzero (I : Ideal.primesOver q (𝓞 K)) : I.val ≠ 0 := by
    letI : I.val.LiesOver q := I.prop.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot hq0 I.val
  let P : Fin (Module.finrank ℚ K) → (Ideal (𝓞 K))⁰ :=
    fun i => ⟨(e i).val, mem_nonZeroDivisors_iff_ne_zero.mpr (hnonzero (e i))⟩
  refine ⟨P, ?_, ?_⟩
  · intro i j h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun J : (Ideal (𝓞 K))⁰ => J.val) h
  · intro i
    letI : (e i).val.IsPrime := (e i).prop.1
    letI : (e i).val.LiesOver q := (e i).prop.2
    apply absNorm_eq_prime_of_inertia_one K p (e i).val
    exact (Ideal.inertiaDegIn_eq_inertiaDeg q (e i).val ℚ K).symm.trans hf

end StrictEUnit
end
