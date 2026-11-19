import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic

noncomputable section
namespace StrictEUnit
variable {k L S : Type*} [CommRing k] [CommRing L] [CommRing S]

/-- Specialize every Laurent coefficient at t^q, keeping the polynomial
variable distinct from the Laurent parameter. -/
def v5LaurentSpecialize (ι : k →+* L) (t : Lˣ) (q : ℕ)
    (h : Polynomial (LaurentPolynomial k)) : Polynomial L :=
  h.map (LaurentPolynomial.eval₂ ι (t ^ q))

theorem v5LaurentSpecialize_monic (ι : k →+* L) (t : Lˣ) (q : ℕ)
    (h : Polynomial (LaurentPolynomial k)) (hh : h.Monic) :
    (v5LaurentSpecialize ι t q h).Monic := hh.map _

@[simp] theorem v5LaurentSpecialize_coeff (ι : k →+* L) (t : Lˣ) (q : ℕ)
    (h : Polynomial (LaurentPolynomial k)) (n : ℕ) :
    (v5LaurentSpecialize ι t q h).coeff n =
      LaurentPolynomial.eval₂ ι (t ^ q) (h.coeff n) := Polynomial.coeff_map _ _

/-- Evaluation of Laurent coefficients commutes with an arbitrary coefficient
homomorphism, including an embedding into the complex numbers. -/
theorem v5Laurent_eval_map (ι : k →+* L) (t : kˣ) (q : ℕ)
    (a : LaurentPolynomial k) :
    ι (LaurentPolynomial.eval₂ (RingHom.id k) (t ^ q) a) =
      LaurentPolynomial.eval₂ ι ((Units.map ι.toMonoidHom t) ^ q) a := by
  induction a using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [map_add, ha, hb]
  | C_mul_T n a =>
    simp only [map_mul, LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T,
      RingHom.id_apply]
    congr 1
    change ((Units.map ι.toMonoidHom ((t ^ q) ^ n) : Lˣ) : L) = _
    rw [map_zpow, map_pow]


/-- Specializing over k and then mapping to L is exactly direct specialization
at the mapped parameter, with the same original monic polynomial. -/
theorem v5LaurentSpecialize_map (ι : k →+* L) (t : kˣ) (q : ℕ)
    (h : Polynomial (LaurentPolynomial k)) :
    (v5LaurentSpecialize (RingHom.id k) t q h).map ι =
      v5LaurentSpecialize ι (Units.map ι.toMonoidHom t) q h := by
  ext n
  simp only [Polynomial.coeff_map, v5LaurentSpecialize_coeff, v5Laurent_eval_map]

/-- Polynomial value evaluation commutes with coefficient mapping. -/
theorem v5LaurentSpecialize_eval_map (ι : k →+* L) (t : kˣ) (q : ℕ)
    (h : Polynomial (LaurentPolynomial k)) (x : k) :
    ι ((v5LaurentSpecialize (RingHom.id k) t q h).eval x) =
      (v5LaurentSpecialize ι (Units.map ι.toMonoidHom t) q h).eval (ι x) := by
  rw [← v5LaurentSpecialize_map]
  rw [Polynomial.eval_map]
  exact (Polynomial.eval₂_hom ι x).symm

/-- An actual algebraic relation specializes to a monic pointwise relation
when evaluation agrees on the Laurent base. The polynomial is not reselected
pointwise: it is the map of the original fixed polynomial h. -/
theorem v5LaurentSpecialize_relation
    (ι : k →+* L) (t : Lˣ) (q : ℕ)
    (b : LaurentPolynomial k →+* S) (ev : S →+* L)
    (hbase : ev.comp b = LaurentPolynomial.eval₂ ι (t ^ q))
    (h : Polynomial (LaurentPolynomial k)) (hh : h.Monic)
    (x : S) (hx : h.eval₂ b x = 0) :
    (v5LaurentSpecialize ι t q h).Monic ∧
      (v5LaurentSpecialize ι t q h).eval (ev x) = 0 := by
  refine ⟨v5LaurentSpecialize_monic ι t q h hh, ?_⟩
  have he := congrArg ev hx
  rw [Polynomial.hom_eval₂, hbase, map_zero] at he
  simpa only [v5LaurentSpecialize, Polynomial.eval_map] using he

end StrictEUnit
#print axioms StrictEUnit.v5LaurentSpecialize_monic
#print axioms StrictEUnit.v5LaurentSpecialize_coeff
#print axioms StrictEUnit.v5Laurent_eval_map
#print axioms StrictEUnit.v5LaurentSpecialize_map
#print axioms StrictEUnit.v5LaurentSpecialize_eval_map
#print axioms StrictEUnit.v5LaurentSpecialize_relation
