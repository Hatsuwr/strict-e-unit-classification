import FiberTensorChart

noncomputable section
set_option maxHeartbeats 800000
open scoped TensorProduct
namespace StrictEUnit
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
variable {k B R H N : Type*} [CommRing k] [CommRing B] [CommRing R]
  [CommRing H] [CommRing N] [Algebra k B] [Algebra k R]
  [Algebra B R] [IsScalarTower k B R] [Algebra k H] [Algebra k N]

def v5OwnTorsorTargetChart (e : R ⊗[B] R ≃ₐ[k] R ⊗[k] H) :
    R ⊗[B] (R ⊗[k] N) ≃ₐ[k] R ⊗[k] (H ⊗[k] N) :=
  ((fiberMixedAssoc (k := k) (B := B) (A := R)).symm.restrictScalars k).trans
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl (R := k) (A₁ := N))).trans
      (Algebra.TensorProduct.assoc k R H N))

@[simp] theorem v5OwnTorsorTargetChart_tmul
    (e : R ⊗[B] R ≃ₐ[k] R ⊗[k] H) (r s : R) (n : N) :
    v5OwnTorsorTargetChart e (r ⊗ₜ[B] (s ⊗ₜ[k] n)) =
      Algebra.TensorProduct.assoc k R H N (e (r ⊗ₜ[B] s) ⊗ₜ[k] n) := by
  have h : (fiberMixedAssoc (k := k) (B := B) (A := R)).symm
      (r ⊗ₜ[B] (s ⊗ₜ[k] n)) = (r ⊗ₜ[B] s) ⊗ₜ[k] n := by
    apply (fiberMixedAssoc (k := k) (B := B) (A := R)).injective
    simp only [AlgEquiv.apply_symm_apply, fiberMixedAssoc_tmul]
  simp only [v5OwnTorsorTargetChart, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply, h]
  rfl

private theorem assoc_smul (r : R) (z : R ⊗[k] H) (n : N) :
    Algebra.TensorProduct.assoc k R H N ((r • z) ⊗ₜ[k] n) =
      r • Algebra.TensorProduct.assoc k R H N (z ⊗ₜ[k] n) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
  | add x y hx hy => simp only [smul_add, TensorProduct.add_tmul, map_add, hx, hy]
  | tmul a h => rfl

private theorem map_smul (δ : H →ₐ[k] H ⊗[k] N) (r : R) (z : R ⊗[k] H) :
    Algebra.TensorProduct.map (AlgHom.id k R) δ (r • z) =
      r • Algebra.TensorProduct.map (AlgHom.id k R) δ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a h => rfl

theorem v5OwnTorsorTargetChart_action
    (e : R ⊗[B] R ≃ₐ[k] R ⊗[k] H) (ρ : R →ₐ[B] R ⊗[k] H)
    (he : ∀ r s, e (r ⊗ₜ[B] s) = r • ρ s) (r : R) (z : R ⊗[k] N) :
    v5OwnTorsorTargetChart e (r ⊗ₜ[B] z) =
      r • Algebra.TensorProduct.assoc k R H N
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy, smul_add]
  | tmul s n =>
    rw [v5OwnTorsorTargetChart_tmul, he]
    exact assoc_smul r (ρ s) n

/-- Own-torsor comparison square from a mixed right-action law. -/
theorem v5OwnTorsorSquare
    (e : R ⊗[B] R ≃ₐ[k] R ⊗[k] H) (ρ : R →ₐ[B] R ⊗[k] H)
    (ρN : R →ₐ[B] R ⊗[k] N) (δ : H →ₐ[k] H ⊗[k] N)
    (he : ∀ r s, e (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ s, Algebra.TensorProduct.assoc k R H N
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) (ρN s)) =
      Algebra.TensorProduct.map (AlgHom.id k R) δ (ρ s))
    (x : R ⊗[B] R) :
    v5OwnTorsorTargetChart e (Algebra.TensorProduct.map (AlgHom.id B R) ρN x) =
      Algebra.TensorProduct.map (AlgHom.id k R) δ (e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r s =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      v5OwnTorsorTargetChart_action e ρ he, hρ, he, map_smul]

/-- Restrict the own action along a quotient (or any algebra map). -/
def v5OwnRestrictedAction (ρ : R →ₐ[B] R ⊗[k] H) (q : H →ₐ[k] N) :
    R →ₐ[B] R ⊗[k] N :=
  (Algebra.TensorProduct.map (AlgHom.id B R) q).comp ρ

/-- Coassociativity gives the mixed law for the restricted right action. -/
theorem v5OwnRestrictedAction_law (ρ : R →ₐ[B] R ⊗[k] H)
    (Δ : H →ₐ[k] H ⊗[k] H) (q : H →ₐ[k] N)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (ρ r)) (r : R) :
    Algebra.TensorProduct.assoc k R H N
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N)
        (v5OwnRestrictedAction ρ q r)) =
      Algebra.TensorProduct.map (AlgHom.id k R)
        ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ) (ρ r) := by
  let F := Algebra.TensorProduct.map (AlgHom.id k R)
    (Algebra.TensorProduct.map (AlgHom.id k H) q)
  have hassoc (z : R ⊗[k] H) (h : H) :
      F (Algebra.TensorProduct.assoc k R H H (z ⊗ₜ[k] h)) =
        Algebra.TensorProduct.assoc k R H N (z ⊗ₜ[k] q h) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | tmul a b => rfl
  have hl (z : R ⊗[k] H) :
      F (Algebra.TensorProduct.assoc k R H H
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) z)) =
      Algebra.TensorProduct.assoc k R H N
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N)
          (Algebra.TensorProduct.map (AlgHom.id B R) q z)) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => exact hassoc (ρ a) b
  have hr (z : R ⊗[k] H) :
      F (Algebra.TensorProduct.map (AlgHom.id k R) Δ z) =
      Algebra.TensorProduct.map (AlgHom.id k R)
        ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, TensorProduct.tmul_zero, TensorProduct.zero_tmul, smul_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b => rfl
  exact (hl (ρ r)).symm.trans ((congrArg F (hρ r)).trans (hr (ρ r)))

/-- The actual restricted own-torsor square follows from the original
coassociativity law, with no extra equivariance hypothesis. -/
theorem v5OwnRestrictedTorsorSquare
    (e : R ⊗[B] R ≃ₐ[k] R ⊗[k] H) (ρ : R →ₐ[B] R ⊗[k] H)
    (Δ : H →ₐ[k] H ⊗[k] H) (q : H →ₐ[k] N)
    (he : ∀ r s, e (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (ρ r)) (x : R ⊗[B] R) :
    v5OwnTorsorTargetChart e
      (Algebra.TensorProduct.map (AlgHom.id B R) (v5OwnRestrictedAction ρ q) x) =
    Algebra.TensorProduct.map (AlgHom.id k R)
      ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ) (e x) :=
  v5OwnTorsorSquare e ρ (v5OwnRestrictedAction ρ q) _ he
    (v5OwnRestrictedAction_law ρ Δ q hρ) x

/-- The target chart retains its left R-algebra structure. -/
def v5OwnTorsorTargetChartR (e : R ⊗[B] R ≃ₐ[R] R ⊗[k] H) :
    R ⊗[B] (R ⊗[k] N) ≃ₐ[R] R ⊗[k] (H ⊗[k] N) :=
  { (v5OwnTorsorTargetChart (e.restrictScalars k)).toRingEquiv with
    commutes' := by
      intro r
      change v5OwnTorsorTargetChart (e.restrictScalars k)
        (r ⊗ₜ[B] ((1 : R) ⊗ₜ[k] (1 : N))) = r ⊗ₜ[k] ((1 : H) ⊗ₜ[k] (1 : N))
      rw [v5OwnTorsorTargetChart_tmul]
      have he : e (r ⊗ₜ[B] (1 : R)) = r ⊗ₜ[k] (1 : H) := e.commutes r
      change Algebra.TensorProduct.assoc k R H N
        (e (r ⊗ₜ[B] (1 : R)) ⊗ₜ[k] (1 : N)) = _
      rw [he]
      rfl }

/-- Left R-algebra form of the restricted comparison square. -/
theorem v5OwnRestrictedTorsorSquareR
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[k] H) (ρ : R →ₐ[B] R ⊗[k] H)
    (Δ : H →ₐ[k] H ⊗[k] H) (q : H →ₐ[k] N)
    (he : ∀ r s, e (r ⊗ₜ[B] s) = r • ρ s)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R H H
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k H) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id k R) Δ (ρ r)) (x : R ⊗[B] R) :
    v5OwnTorsorTargetChartR e
      (Algebra.TensorProduct.map (AlgHom.id R R) (v5OwnRestrictedAction ρ q) x) =
    Algebra.TensorProduct.map (AlgHom.id R R)
      ((Algebra.TensorProduct.map (AlgHom.id k H) q).comp Δ) (e x) :=
  v5OwnRestrictedTorsorSquare (e.restrictScalars k) ρ Δ q he hρ x

/-- The trivial/include-left map gives the second equalizer square. -/
theorem v5OwnTrivialTorsorSquareR
    (e : R ⊗[B] R ≃ₐ[R] R ⊗[k] H) (x : R ⊗[B] R) :
    v5OwnTorsorTargetChartR e
      (Algebra.TensorProduct.map (AlgHom.id R R)
        (Algebra.TensorProduct.includeLeft : R →ₐ[B] R ⊗[k] N) x) =
    Algebra.TensorProduct.map (AlgHom.id R R)
      (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) (e x) := by
  have h (z : R ⊗[k] H) :
      Algebra.TensorProduct.assoc k R H N (z ⊗ₜ[k] (1 : N)) =
      Algebra.TensorProduct.map (AlgHom.id R R)
        (Algebra.TensorProduct.includeLeft : H →ₐ[k] H ⊗[k] N) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [TensorProduct.zero_tmul, map_zero]
    | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
    | tmul a b => rfl
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    change v5OwnTorsorTargetChart (e.restrictScalars k) (a ⊗ₜ[B] (b ⊗ₜ[k] (1 : N))) = _
    rw [v5OwnTorsorTargetChart_tmul]
    exact h (e (a ⊗ₜ[B] b))

end StrictEUnit
#print axioms StrictEUnit.v5OwnTorsorTargetChart
#print axioms StrictEUnit.v5OwnTorsorTargetChart_action
#print axioms StrictEUnit.v5OwnTorsorSquare

#print axioms StrictEUnit.v5OwnRestrictedAction
#print axioms StrictEUnit.v5OwnRestrictedAction_law
#print axioms StrictEUnit.v5OwnRestrictedTorsorSquare

#print axioms StrictEUnit.v5OwnTorsorTargetChartR
#print axioms StrictEUnit.v5OwnRestrictedTorsorSquareR

#print axioms StrictEUnit.v5OwnTrivialTorsorSquareR
