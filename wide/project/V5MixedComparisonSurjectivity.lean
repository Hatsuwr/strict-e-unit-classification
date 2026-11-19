import V5HorizontalCoordinates
import PVConstantAlgebra
import MixedRelativeTensorDerivation

open scoped TensorProduct
open TensorProduct
noncomputable section
namespace StrictEUnit

variable {k B R S n : Type*} [CommRing k] [CommRing B] [CommRing R] [CommRing S]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]
  [Algebra k S] [Algebra B S] [IsScalarTower k B S]
  [Fintype n] [DecidableEq n]

/-- Multiplication into the mixed tensor product, using the actual constants
of its derivation, not the constants of the PV torsor's tensor square. -/
def v5MixedConstantMultiplication (d : Derivation k (R ⊗[B] S) (R ⊗[B] S)) :
    R ⊗[k] derivationConstants d →ₐ[R] R ⊗[B] S :=
  Algebra.TensorProduct.lift (Algebra.ofId R (R ⊗[B] S))
    (derivationConstants d).val (fun _ _ => Commute.all _ _)

abbrev v5MixedLeftMatrix (Y : (Matrix n n R)ˣ) : (Matrix n n (R ⊗[B] S))ˣ :=
  Units.map (Algebra.TensorProduct.includeLeftRingHom (R := B) (A := R) (B := S)).mapMatrix.toMonoidHom Y

theorem v5_mixedConstantMultiplication_surjective
    (d : Derivation k (R ⊗[B] S) (R ⊗[B] S))
    (A : Matrix n n (R ⊗[B] S)) (Y : (Matrix n n R)ˣ) (v : n → S)
    (hY : matrixDerivative d (v5MixedLeftMatrix (B := B) (S := S) Y : Matrix n n (R ⊗[B] S)) =
      A * (v5MixedLeftMatrix (B := B) (S := S) Y : Matrix n n (R ⊗[B] S)))
    (hv : ∀ i, d ((1 : R) ⊗ₜ[B] v i) = (A.mulVec (fun j => (1 : R) ⊗ₜ[B] v j)) i)
    (hgen : Algebra.adjoin B (Set.range v) = ⊤) :
    Function.Surjective (v5MixedConstantMultiplication d) := by
  let μ := v5MixedConstantMultiplication d
  let L := v5MixedLeftMatrix (B := B) (S := S) Y
  let w : n → R ⊗[B] S := fun j => (1 : R) ⊗ₜ[B] v j
  let c := (↑L⁻¹ : Matrix n n (R ⊗[B] S)).mulVec w
  obtain ⟨hc, hw⟩ := v5_horizontal_coordinates d A L w hY hv
  have hleft (r : R) : (r ⊗ₜ[B] (1 : S)) ∈ μ.range := by
    refine ⟨r ⊗ₜ[k] (1 : derivationConstants d), ?_⟩
    change (r ⊗ₜ[B] (1 : S)) * 1 = _
    simp
  have hconst (i : n) : c i ∈ μ.range := by
    refine ⟨(1 : R) ⊗ₜ[k] (⟨c i, hc i⟩ : derivationConstants d), ?_⟩
    change ((1 : R) ⊗ₜ[B] (1 : S)) * c i = _
    rw [← Algebra.TensorProduct.one_def, one_mul]
  let ρ : S →ₐ[B] R ⊗[B] S := Algebra.TensorProduct.includeRight
  let K : Subalgebra B S := (μ.range.restrictScalars B).comap ρ
  have hK : K = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Algebra.adjoin_le
    rintro _ ⟨i, rfl⟩
    change w i ∈ μ.range
    rw [← hw]
    change (∑ j, ((Y : Matrix n n R) i j ⊗ₜ[B] (1 : S)) * c j) ∈ μ.range
    exact μ.range.sum_mem (fun j _ => μ.range.mul_mem (hleft _) (hconst j))
  have hright (s : S) : (1 : R) ⊗ₜ[B] s ∈ μ.range := by
    change s ∈ K
    rw [hK]
    trivial
  intro z
  change z ∈ μ.range
  induction z using TensorProduct.induction_on with
  | zero => exact μ.range.zero_mem
  | tmul r s =>
    have ht : r ⊗ₜ[B] s = (r ⊗ₜ[B] (1 : S)) * ((1 : R) ⊗ₜ[B] s) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [ht]
    exact μ.range.mul_mem (hleft _) (hright _)
  | add x y hx hy => exact μ.range.add_mem hx hy

end StrictEUnit
#print axioms StrictEUnit.v5_mixedConstantMultiplication_surjective
