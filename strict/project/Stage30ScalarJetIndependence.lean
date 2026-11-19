import Stage30SolutionIndependence

/-! A scalar family solving one nondegenerate scalar differential equation
has independent derivative-jet columns. The zeroth row supplies independence
over constants; the same-system theorem then supplies ambient independence.
No general Wronskian criterion or arithmetic basis-existence theorem is used. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [-instance] Polynomial.commSemiring
open scoped BigOperators Matrix
namespace StrictEUnit
variable {k E ι : Type*} [Field k] [Field E] [Algebra k E]

/-- The literal finite jet of iterates of a specified differentiation map. -/
def stage30_derivativeJet (d : E → E) (m : ℕ) (y : E) : Fin m → E :=
  fun i => d^[i.val] y

omit [Field E] in
/-- Row zero is the original scalar, for strictly positive jet length. -/
theorem stage30_derivativeJet_zero (d : E → E) (m : ℕ) (hm : 0 < m) (y : E) :
    stage30_derivativeJet d m y ⟨0, hm⟩ = y := rfl

/-- Scalar independence gives jet-column independence just by projecting a
finite relation to row zero. No differential equation is needed for this step. -/
theorem stage30_derivativeJet_linearIndependent (d : E → E) (m : ℕ) (hm : 0 < m)
    (y : ι → E) (hy : LinearIndependent k y) :
    LinearIndependent k (fun j => stage30_derivativeJet d m (y j)) := by
  classical
  apply linearIndependent_iff'.mpr
  intro s f hf
  have hzero := congrFun hf (⟨0, hm⟩ : Fin m)
  have hrel : ∑ j ∈ s, f j • y j = 0 := by
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      stage30_derivativeJet_zero] using hzero
  exact linearIndependent_iff'.mp hy s f hrel

/-- The actual ordinary companion over the ambient field, with the leading
coefficient divided out only under an explicit nonzero-leading hypothesis. -/
def stage30_scalarCompanion (m : ℕ) (a : Fin (m + 1) → E) : Matrix (Fin m) (Fin m) E :=
  fun i j => if i.val + 1 < m then
    if j.val = i.val + 1 then 1 else 0
  else -(a (Fin.last m))⁻¹ * a j.castSucc

/-- A genuine scalar equation implies the companion vector equation for its
literal derivative jet. The vector equation is a conclusion, not an input. -/
theorem stage30_derivativeJet_solution (d : Derivation k E E) (m : ℕ)
    (a : Fin (m + 1) → E) (ha : a (Fin.last m) ≠ 0) (y : E)
    (hy : ∑ j, a j * (d : E → E)^[j.val] y = 0) :
    ∀ i, d (stage30_derivativeJet d m y i) =
      ∑ l, stage30_scalarCompanion m a i l * stage30_derivativeJet d m y l := by
  intro i
  simp only [stage30_derivativeJet, ← Function.iterate_succ_apply', stage30_scalarCompanion]
  by_cases hi : i.val + 1 < m
  · let j : Fin m := ⟨i.val + 1, hi⟩
    have hj (l : Fin m) : l.val = i.val + 1 ↔ l = j :=
      ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp only [hi, if_true, hj, ite_mul, one_mul, zero_mul]
    simp [j]
  · have him : i.val + 1 = m := by omega
    simp only [hi, if_false]
    change (d : E → E)^[i.val + 1] y = _
    rw [him]
    have he := hy
    rw [Fin.sum_univ_castSucc] at he
    simp only [Fin.coe_castSucc, Fin.val_last] at he
    have ht := congrArg (fun x : E => (a (Fin.last m))⁻¹ * x) he
    dsimp only at ht
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul, mul_zero] at ht
    have hs : ∑ l : Fin m, -(a (Fin.last m))⁻¹ * a l.castSucc * (d : E → E)^[l.val] y =
        -((a (Fin.last m))⁻¹ * ∑ l : Fin m, a l.castSucc * (d : E → E)^[l.val] y) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro l hl
      ring
    rw [hs]
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using ht)

/-- For solutions of one nondegenerate scalar equation, independent scalars
over constants produce derivative-jet columns independent over the field. -/
theorem stage30_scalar_solution_jets_linearIndependent (d : Derivation k E E)
    (hconstants : ∀ a : E, d a = 0 → ∃ c : k, algebraMap k E c = a)
    (m : ℕ) (hm : 0 < m) (a : Fin (m + 1) → E) (ha : a (Fin.last m) ≠ 0)
    (y : ι → E) (hy : ∀ j, ∑ l, a l * (d : E → E)^[l.val] (y j) = 0)
    (hli : LinearIndependent k y) :
    LinearIndependent E (fun j => stage30_derivativeJet d m (y j)) :=
  stage30_solution_columns_linearIndependent d hconstants (stage30_scalarCompanion m a)
    _ (fun j => stage30_derivativeJet_solution d m a ha (y j) (hy j))
    (stage30_derivativeJet_linearIndependent d m hm y hli)

/-- Nonzero square derivative-jet determinant is proved from scalar
independence and the common scalar equation, with no determinant premise. -/
theorem stage30_scalar_solution_jet_det_ne_zero (d : Derivation k E E)
    (hconstants : ∀ a : E, d a = 0 → ∃ c : k, algebraMap k E c = a)
    (m : ℕ) (hm : 0 < m) (a : Fin (m + 1) → E) (ha : a (Fin.last m) ≠ 0)
    (y : Fin m → E) (hy : ∀ j, ∑ l, a l * (d : E → E)^[l.val] (y j) = 0)
    (hli : LinearIndependent k y) :
    (Matrix.of (fun i j : Fin m => stage30_derivativeJet d m (y j) i)).det ≠ 0 := by
  apply stage30_solution_matrix_det_ne_zero d hconstants (stage30_scalarCompanion m a)
  · exact fun j => stage30_derivativeJet_solution d m a ha (y j) (hy j)
  · exact stage30_derivativeJet_linearIndependent d m hm y hli

/-- Scalar jet nondegeneracy for a nonzero rescaling of the actual formal
ambient derivation. The supplied derivation must be identified with ordinary
z-differentiation separately before calling these ordinary z-jets. -/
theorem stage30_scaled_formal_jet_det_ne_zero [CharZero k]
    (N : ℕ) (hN : N ≠ 0) (u : RatFunc (LaurentSeries k)) (hu : u ≠ 0)
    (m : ℕ) (hm : 0 < m) (a : Fin (m + 1) → RatFunc (LaurentSeries k))
    (ha : a (Fin.last m) ≠ 0) (y : Fin m → RatFunc (LaurentSeries k))
    (hy : ∀ j, ∑ l, a l *
      ((u • formalAmbientDerivation (k := k) N hN : Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k))) :
        RatFunc (LaurentSeries k) → RatFunc (LaurentSeries k))^[l.val] (y j) = 0)
    (hli : LinearIndependent k y) :
    (Matrix.of (fun i j : Fin m =>
      stage30_derivativeJet (E := RatFunc (LaurentSeries k))
        (u • formalAmbientDerivation (k := k) N hN : Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k))) m (y j) i)).det ≠ 0 :=
  stage30_scalar_solution_jet_det_ne_zero (k := k) (E := RatFunc (LaurentSeries k))
    (u • formalAmbientDerivation (k := k) N hN : Derivation k (RatFunc (LaurentSeries k)) (RatFunc (LaurentSeries k)))
    (fun x => (stage30_scaled_formal_constants N hN u hu x).mp) m hm a ha y hy hli

end StrictEUnit
