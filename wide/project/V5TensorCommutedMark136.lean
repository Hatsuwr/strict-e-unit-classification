import V5MixedMarkedTensor135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
def v5TensorCommRing136 (B U V : Type*) [CommRing B] [CommRing U] [CommRing V]
    [Algebra B U] [Algebra B V] : CommRing (U ⊗[B] V) := inferInstance
variable {k B L W C F : Type*}
  [CommRing k] [CommRing B] [CommRing L] [CommRing W] [CommRing C] [CommRing F]
  [Algebra k B] [Algebra k L] [Algebra B L] [IsScalarTower k B L]
  [Algebra k W] [Algebra B W] [Algebra k C]
/-- Pure-tensor agreement suffices to compare an analytic realization after
commuting the tensor factors with the existing marked tensor point. -/
theorem v5TensorCommutedMark136
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (η : W ⊗[B] L →+* F) (ev : F →+* C)
    (hη : ∀ w l, ev (η (w ⊗ₜ[B] l)) = algebraMap k C (pL l) * pW w)
    (b : L ⊗[B] W) :
    ev (η (Algebra.TensorProduct.comm B L W b)) =
      v5MixedMarkedTensor135 pL pW hB b := by
  induction b using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul l w =>
    change ev (η (w ⊗ₜ[B] l)) = _
    rw [hη, v5MixedMarkedTensor135_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]
/-- Literal point evaluation on a function subalgebra as a ring homomorphism. -/
def v5FunctionSubalgebraEval136 {ι : Type*}
    [Algebra k (ι → C)] (S : Subalgebra k (ι → C)) (i : ι) : S →+* C :=
  (Pi.evalRingHom (fun _ : ι => C) i).comp S.val.toRingHom
theorem v5RealizationCommutedMark136 {I : Type*} [Monoid I]
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (wval : W → I → C) (lval : L → I → C) (fval : I → F →+* C)
    (hw : ∀ w, wval w 1 = pW w)
    (hl : ∀ l, lval l 1 = algebraMap k C (pL l)) (q : ℕ) :
    ∀ (η : W ⊗[B] L →+* F),
      (∀ w l z, fval z (η (w ⊗ₜ[B] l)) = wval w (z^q) * lval l z) →
      ∀ b : L ⊗[B] W, fval 1 (η (Algebra.TensorProduct.comm B L W b)) =
        v5MixedMarkedTensor135 pL pW hB b := by
  intro η hη b
  apply v5TensorCommutedMark136 pL pW hB η (fval 1) _ b
  intro w l
  rw [hη, one_pow, hw, hl, mul_comm]
theorem v5RealizationCommutedInverseMark136 {I : Type*} [Monoid I]
    (pL : L →ₐ[k] k) (pW : W →ₐ[k] C)
    (hB : ∀ b, algebraMap k C (pL (algebraMap B L b)) = pW (algebraMap B W b))
    (wval : W → I → C) (lval : L → I → C) (fval : I → F →+* C)
    (hw : ∀ w, wval w 1 = pW w)
    (hl : ∀ l, lval l 1 = algebraMap k C (pL l)) (q : ℕ) :
    ∀ (η : W ⊗[B] L →+* F),
      (∀ w l z, fval z (η (w ⊗ₜ[B] l)) = wval w (z^q) * lval l z) →
      ∀ b : (L ⊗[B] W)ˣ,
        fval 1 (η (Algebra.TensorProduct.comm B L W (↑b⁻¹ : L ⊗[B] W))) =
          v5MixedMarkedTensor135 pL pW hB (↑b⁻¹ : L ⊗[B] W) := by
  intro η hη b
  exact v5RealizationCommutedMark136 pL pW hB wval lval fval hw hl q η hη _
end StrictEUnit
#print axioms StrictEUnit.v5TensorCommutedMark136
#print axioms StrictEUnit.v5FunctionSubalgebraEval136

#print axioms StrictEUnit.v5TensorCommRing136

#print axioms StrictEUnit.v5RealizationCommutedMark136
#print axioms StrictEUnit.v5RealizationCommutedInverseMark136
