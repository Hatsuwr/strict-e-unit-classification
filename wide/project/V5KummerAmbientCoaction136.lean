import V5KummerAmbientMap136
noncomputable section
open scoped TensorProduct
namespace StrictEUnit
set_option maxHeartbeats 600000
set_option maxRecDepth 1600
set_option synthInstance.maxHeartbeats 20000
attribute [-instance] TensorProduct.leftModule
attribute [local instance 2000] Algebra.toModule
local instance algebraSMulCommAmbientCoact136 (A B C : Type*) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A C] [Algebra B C] : SMulCommClass A B C :=
  ⟨fun a b c => by simp only [Algebra.smul_def]; exact mul_left_comm _ _ _⟩
variable {k B T L R W N : Type*}
  [CommRing k] [CommRing B] [CommRing T] [CommRing L] [CommRing R]
  [CommRing W] [CommRing N]
  [Algebra k B] [Algebra k T] [Algebra k L] [Algebra k R] [Algebra k W] [Algebra k N]
  [Algebra B T] [Algebra B L] [Algebra B R] [Algebra B W]
  [Algebra T L] [Algebra T R]
  [IsScalarTower k B T] [IsScalarTower k B L] [IsScalarTower k B R] [IsScalarTower k B W]
  [IsScalarTower k T L] [IsScalarTower k T R]
  [IsScalarTower B T L] [IsScalarTower B T R]

theorem v5KummerAmbientShuffle136 (w : W) (z : R ⊗[k] N) :
    v5MixedCoactionShuffle (k := k) (B := L)
      (((1 : L) ⊗ₜ[B] w) ⊗ₜ[L]
        Algebra.TensorProduct.map
          (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R)) (AlgHom.id k N) z) =
      Algebra.TensorProduct.map
        (v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W))
        (AlgHom.id k N)
        (v5MixedCoactionShuffle (k := k) (B := B) (w ⊗ₜ[B] z)) := by
  let shL := v5MixedCoactionShuffle (k := k) (B := L)
    (R := L ⊗[T] R) (S := L ⊗[B] W) (H := N)
  let shB := v5MixedCoactionShuffle (k := k) (B := B) (R := R) (S := W) (H := N)
  let mR := Algebra.TensorProduct.map
    (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R)) (AlgHom.id k N)
  let mM := Algebra.TensorProduct.map
    (v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W))
    (AlgHom.id k N)
  change shL (((1 : L) ⊗ₜ[B] w) ⊗ₜ[L] mR z) = mM (shB (w ⊗ₜ[B] z))
  induction z using TensorProduct.induction_on with
  | zero =>
    have hR : mR 0 = 0 := mR.map_zero'
    have hSL : shL 0 = 0 := shL.toAlgHom.map_zero'
    have hSB : shB 0 = 0 := shB.toAlgHom.map_zero'
    have hM : mM 0 = 0 := mM.map_zero'
    rw [hR, TensorProduct.tmul_zero, hSL, TensorProduct.tmul_zero, hSB, hM]
  | add x y hx hy =>
    have hR : mR (x + y) = mR x + mR y := mR.map_add' x y
    have hSL : shL (((1 : L) ⊗ₜ[B] w) ⊗ₜ[L] mR x + ((1 : L) ⊗ₜ[B] w) ⊗ₜ[L] mR y) =
      shL (((1 : L) ⊗ₜ[B] w) ⊗ₜ[L] mR x) + shL (((1 : L) ⊗ₜ[B] w) ⊗ₜ[L] mR y) := shL.toAlgHom.map_add' _ _
    have hSB : shB (w ⊗ₜ[B] x + w ⊗ₜ[B] y) = shB (w ⊗ₜ[B] x) + shB (w ⊗ₜ[B] y) := shB.toAlgHom.map_add' _ _
    have hM : mM (shB (w ⊗ₜ[B] x) + shB (w ⊗ₜ[B] y)) =
      mM (shB (w ⊗ₜ[B] x)) + mM (shB (w ⊗ₜ[B] y)) := mM.map_add' _ _
    rw [hR, TensorProduct.tmul_add, hSL, TensorProduct.tmul_add, hSB, hM, hx, hy]
  | tmul r n =>
    simp only [shL, shB, mR, mM, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      v5MixedCoactionShuffle_tmul, v5KummerAmbientMap136_tmul]
    rfl

/-- The actual old-to-Kummer ambient map is equivariant. -/
theorem v5KummerAmbientCoaction136 (ρ : R →ₐ[T] R ⊗[k] N) (z : R ⊗[B] W) :
    v5MixedRelativeCoaction (S := L ⊗[B] W) (v5KummerCoaction135 (L := L) ρ)
      (v5KummerAmbientMap136 (k := k) (T := T) (L := L) z) =
      Algebra.TensorProduct.map
        (v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W))
        (AlgHom.id k N)
        (v5MixedRelativeCoaction (S := W) (ρ.restrictScalars B) z) := by
  let Γ := v5KummerAmbientMap136 (k := k) (B := B) (T := T) (L := L) (R := R) (W := W)
  let δL := v5MixedRelativeCoaction (S := L ⊗[B] W) (v5KummerCoaction135 (L := L) ρ)
  let δB := v5MixedRelativeCoaction (S := W) (ρ.restrictScalars B)
  let mM := Algebra.TensorProduct.map Γ (AlgHom.id k N)
  change δL (Γ z) = mM (δB z)
  induction z using TensorProduct.induction_on with
  | zero =>
    have hΓ : Γ 0 = 0 := Γ.map_zero'
    have hδL : δL 0 = 0 := δL.map_zero'
    have hδB : δB 0 = 0 := δB.map_zero'
    have hM : mM 0 = 0 := mM.map_zero'
    rw [hΓ, hδL, hδB, hM]
  | add x y hx hy =>
    have hΓ : Γ (x + y) = Γ x + Γ y := Γ.map_add' _ _
    have hδL : δL (Γ x + Γ y) = δL (Γ x) + δL (Γ y) := δL.map_add' _ _
    have hδB : δB (x + y) = δB x + δB y := δB.map_add' _ _
    have hM : mM (δB x + δB y) = mM (δB x) + mM (δB y) := mM.map_add' _ _
    rw [hΓ, hδL, hδB, hM, hx, hy]
  | tmul r w =>
    simp only [Γ, δL, δB, mM, v5KummerAmbientMap136_tmul, v5MixedRelativeCoaction_tmul]
    have hρ : v5KummerCoaction135 (L := L) ρ ((1 : L) ⊗ₜ[T] r) =
        Algebra.TensorProduct.map
          (v5KummerOwnMap135 (k := k) (T := T) (L := L) (R := R)) (AlgHom.id k N) (ρ r) :=
      v5KummerCoaction135_includeRight ρ r
    rw [hρ]
    exact v5KummerAmbientShuffle136 w (ρ r)

/-- Prescribed character weights pass to the actual Kummer ambient image. -/
theorem v5KummerAmbientWeight136 (ρ : R →ₐ[T] R ⊗[k] N)
    (z : R ⊗[B] W) (χ : N)
    (hz : v5MixedRelativeCoaction (S := W) (ρ.restrictScalars B) z = z ⊗ₜ[k] χ) :
    v5MixedRelativeCoaction (S := L ⊗[B] W) (v5KummerCoaction135 (L := L) ρ)
      (v5KummerAmbientMap136 (k := k) (T := T) (L := L) z) =
      v5KummerAmbientMap136 (k := k) (T := T) (L := L) z ⊗ₜ[k] χ := by
  rw [v5KummerAmbientCoaction136, hz, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- In particular the original reciprocal unit has the same quotient character
in the Kummer ambient. -/
theorem v5KummerAmbientUnitWeight136 (ρ : R →ₐ[T] R ⊗[k] N)
    (u : (R ⊗[B] W)ˣ) (χ : Nˣ)
    (hu : v5MixedRelativeCoaction (S := W) (ρ.restrictScalars B) (u : R ⊗[B] W) =
      (u : R ⊗[B] W) ⊗ₜ[k] (χ : N)) :
    v5MixedRelativeCoaction (S := L ⊗[B] W) (v5KummerCoaction135 (L := L) ρ)
      (Units.map (v5KummerAmbientMap136 (k := k) (T := T) (L := L)).toMonoidHom u :
        (L ⊗[T] R) ⊗[L] (L ⊗[B] W)) =
      (Units.map (v5KummerAmbientMap136 (k := k) (T := T) (L := L)).toMonoidHom u :
        (L ⊗[T] R) ⊗[L] (L ⊗[B] W)) ⊗ₜ[k] (χ : N) :=
  v5KummerAmbientWeight136 ρ (u : R ⊗[B] W) (χ : N) hu
end StrictEUnit
#print axioms StrictEUnit.v5KummerAmbientCoaction136
#print axioms StrictEUnit.v5KummerAmbientWeight136
#print axioms StrictEUnit.v5KummerAmbientUnitWeight136
