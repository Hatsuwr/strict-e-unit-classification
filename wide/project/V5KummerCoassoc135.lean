import V5KummerCoaction135
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
attribute [local instance 100] TensorProduct.leftModule
local instance algebraSMulCommAssoc135 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k T L R N : Type*}
  [CommRing k] [CommRing T] [CommRing L] [CommRing R] [CommRing N]
  [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k N]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k T L] [IsScalarTower k T R]

def v5KummerOwnMap135 : R →ₐ[k] L ⊗[T] R :=
  (Algebra.TensorProduct.includeRight : R →ₐ[T] L ⊗[T] R).restrictScalars k

theorem v5KummerTensorAssoc135_includeRight (z : R ⊗[k] N) :
    (v5KummerTensorAssoc135 (k := k) (T := T) (L := L) (R := R) (N := N)).symm
      ((1 : L) ⊗ₜ[T] z) =
    Algebra.TensorProduct.map (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R))
      (AlgHom.id k N) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [TensorProduct.tmul_zero, map_zero]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul r n => rfl

theorem v5KummerCoaction135_includeRight (ρ : R →ₐ[T] R ⊗[k] N) (r : R) :
    v5KummerCoaction135 (k := k) (T := T) (L := L) (R := R) (N := N) ρ
      (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R) r) =
      Algebra.TensorProduct.map (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R))
        (AlgHom.id k N) (ρ r) :=
  v5KummerTensorAssoc135_includeRight _

theorem v5KummerCoaction135_coassoc
    (ρ : R →ₐ[T] R ⊗[k] N) (Δ : N →ₐ[k] N ⊗[k] N)
    (hρ : ∀ r, Algebra.TensorProduct.assoc k R N N
      (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) (ρ r)) =
      Algebra.TensorProduct.map (AlgHom.id R R) Δ (ρ r))
    (x : L ⊗[T] R) :
    Algebra.TensorProduct.assoc k (L ⊗[T] R) N N
      (Algebra.TensorProduct.map ((v5KummerCoaction135 ρ).restrictScalars k)
        (AlgHom.id k N) (v5KummerCoaction135 ρ x)) =
      Algebra.TensorProduct.map (AlgHom.id (L ⊗[T] R) (L ⊗[T] R)) Δ
        (v5KummerCoaction135 ρ x) := by
  let γ : R →ₐ[k] L ⊗[T] R := v5KummerOwnMap135
  let ρL := v5KummerCoaction135 (L := L) ρ
  let F : L ⊗[T] R →ₗ[L] (L ⊗[T] R) ⊗[k] (N ⊗[k] N) :=
    (TensorProduct.AlgebraTensorModule.assoc k k L (L ⊗[T] R) N N).toLinearMap.comp
      ((Algebra.TensorProduct.map ρL (AlgHom.id k N)).toLinearMap.comp ρL.toLinearMap)
  let G : L ⊗[T] R →ₗ[L] (L ⊗[T] R) ⊗[k] (N ⊗[k] N) :=
    (Algebra.TensorProduct.map (AlgHom.id L (L ⊗[T] R)) Δ).toLinearMap.comp ρL.toLinearMap
  have hA (z : (R ⊗[k] N) ⊗[k] N) :
      Algebra.TensorProduct.assoc k (L ⊗[T] R) N N
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map γ (AlgHom.id k N)) (AlgHom.id k N) z) =
      Algebra.TensorProduct.map γ (AlgHom.id k (N ⊗[k] N))
        (Algebra.TensorProduct.assoc k R N N z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul z n =>
      induction z using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.zero_tmul, map_zero]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul r m => rfl
  have hleft (z : R ⊗[k] N) :
      Algebra.TensorProduct.map (ρL.restrictScalars k) (AlgHom.id k N)
        (Algebra.TensorProduct.map γ (AlgHom.id k N) z) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.map γ (AlgHom.id k N)) (AlgHom.id k N)
        (Algebra.TensorProduct.map (ρ.restrictScalars k) (AlgHom.id k N) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r n =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      change ρL (γ r) ⊗ₜ[k] n = _
      rw [show ρL (γ r) = Algebra.TensorProduct.map γ (AlgHom.id k N) (ρ r) from
        v5KummerCoaction135_includeRight ρ r]
      rfl
  have hright (z : R ⊗[k] N) :
      Algebra.TensorProduct.map γ (AlgHom.id k (N ⊗[k] N))
        (Algebra.TensorProduct.map (AlgHom.id R R) Δ z) =
      Algebra.TensorProduct.map (AlgHom.id (L ⊗[T] R) (L ⊗[T] R)) Δ
        (Algebra.TensorProduct.map γ (AlgHom.id k N) z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul r n => rfl
  have hgen (r : R) : F ((1 : L) ⊗ₜ[T] r) = G ((1 : L) ⊗ₜ[T] r) := by
    change Algebra.TensorProduct.assoc k (L ⊗[T] R) N N
      (Algebra.TensorProduct.map (ρL.restrictScalars k) (AlgHom.id k N) (ρL (γ r))) =
      Algebra.TensorProduct.map (AlgHom.id (L ⊗[T] R) (L ⊗[T] R)) Δ (ρL (γ r))
    rw [show ρL (γ r) = Algebra.TensorProduct.map γ (AlgHom.id k N) (ρ r) from
      v5KummerCoaction135_includeRight ρ r, hleft, hA, hρ, hright]
  have hFG : F = G := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro l r
    have hl : l ⊗ₜ[T] r = l • ((1 : L) ⊗ₜ[T] r) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hl, F.map_smul, G.map_smul, hgen]
  change F x = G x
  rw [hFG]
end StrictEUnit
#print axioms StrictEUnit.v5KummerCoaction135_coassoc
