import FundamentalMatrixConstants
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! Actual connection matrices from finite generators and finite relations.
No local freeness or projectivity is asserted. -/
noncomputable section
namespace StrictEUnit
variable {k B M n : Type*} [CommRing k] [CommRing B] [Algebra k B]
  [AddCommGroup M] [Module B M] [Module k M] [IsScalarTower k B M]
  [Fintype n] [DecidableEq n]

def liftedFreeConnection (δ : Derivation k B B) (P : n → (n → B)) (x : n → B) : n → B :=
  (fun i => δ (x i)) + ∑ j, x j • P j

def liftedFreeConnectionLinear (δ : Derivation k B B) (P : n → (n → B)) :
    (n → B) →ₗ[k] (n → B) where
  toFun := liftedFreeConnection δ P
  map_add' x y := by
    ext i
    simp [liftedFreeConnection, add_smul, Finset.sum_add_distrib, add_assoc, add_comm, add_left_comm]
  map_smul' c x := by
    ext i
    simp [liftedFreeConnection, smul_add, Finset.smul_sum, smul_smul, mul_smul]

@[simp] theorem liftedFreeConnectionLinear_apply (δ : Derivation k B B)
    (P : n → (n → B)) (x : n → B) :
    liftedFreeConnectionLinear δ P x = liftedFreeConnection δ P x := rfl

theorem liftedFreeConnection_compatible
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x)
    (v : n → M) (P : n → (n → B))
    (hP : ∀ j, Fintype.linearCombination B v (P j) = D (v j)) (x : n → B) :
    Fintype.linearCombination B v (liftedFreeConnection δ P x) =
      D (Fintype.linearCombination B v x) := by
  simp only [liftedFreeConnection, map_add, map_sum, map_smul, hP,
    Fintype.linearCombination_apply, hD, Finset.sum_add_distrib]

theorem liftedFreeConnection_kernel_stable
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x)
    (v : n → M) (P : n → (n → B))
    (hP : ∀ j, Fintype.linearCombination B v (P j) = D (v j))
    (x : n → B) (hx : x ∈ LinearMap.ker (Fintype.linearCombination B v)) :
    liftedFreeConnection δ P x ∈ LinearMap.ker (Fintype.linearCombination B v) := by
  change Fintype.linearCombination B v _ = 0
  rw [liftedFreeConnection_compatible δ D hD v P hP x,
    show Fintype.linearCombination B v x = 0 from hx, map_zero]

theorem liftedFreeConnection_leibniz (δ : Derivation k B B) (P : n → (n → B))
    (b:B) (x:n→B) :
    liftedFreeConnection δ P (b • x) = δ b • x + b • liftedFreeConnection δ P x := by
  ext i
  simp [liftedFreeConnection, Derivation.leibniz, Finset.mul_sum, mul_add,
    mul_assoc, mul_comm, mul_left_comm, add_assoc, add_comm, add_left_comm]

theorem exists_liftedFreeConnection
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (v : n → M) (hv : Submodule.span B (Set.range v) = ⊤) :
    ∃ P : n → (n → B), ∀ j, Fintype.linearCombination B v (P j) = D (v j) := by
  have hπ : Function.Surjective (Fintype.linearCombination B v) := by
    apply LinearMap.range_eq_top.mp
    rw [Fintype.range_linearCombination, hv]
  exact ⟨fun j => Classical.choose (hπ (D (v j))),
    fun j => Classical.choose_spec (hπ (D (v j)))⟩

/-- Finite relations have a genuine connection matrix, obtained by expressing
the derivatives of the relation generators in the same finite generating family. -/
theorem finite_differential_presentation [IsNoetherianRing B] [Module.Finite B M]
    (δ : Derivation k B B) (D : M →ₗ[k] M)
    (hD : ∀ b x, D (b • x) = δ b • x + b • D x) :
    ∃ (n m : ℕ) (v : Fin n → M)
      (A : Matrix (Fin n) (Fin m) B) (P : Matrix (Fin n) (Fin n) B)
      (Q : Matrix (Fin m) (Fin m) B),
      Function.Surjective (Fintype.linearCombination B v) ∧
      Submodule.span B (Set.range fun j : Fin m => fun i : Fin n => A i j) =
        LinearMap.ker (Fintype.linearCombination B v) ∧
      (∀ j, Fintype.linearCombination B v (fun i => P i j) = D (v j)) ∧
      (∀ i j, δ (A i j) = (A * Q - P * A) i j) := by
  obtain ⟨n,v,hv⟩ := Module.Finite.exists_fin (R := B) (M := M)
  obtain ⟨P,hP⟩ := exists_liftedFreeConnection δ D v hv
  let π := Fintype.linearCombination B v
  let K := LinearMap.ker π
  have hπ : Function.Surjective π := by
    apply LinearMap.range_eq_top.mp
    exact (Fintype.range_linearCombination B v).trans hv
  obtain ⟨m,w,hw⟩ := Module.Finite.exists_fin (R := B) (M := K)
  have hW : Function.Surjective (Fintype.linearCombination B w) := by
    apply LinearMap.range_eq_top.mp
    exact (Fintype.range_linearCombination B w).trans hw
  let dw (j : Fin m) : K := ⟨liftedFreeConnection δ P (w j),
    liftedFreeConnection_kernel_stable δ D hD v P hP (w j) (w j).property⟩
  choose Q hQ using fun j => hW (dw j)
  refine ⟨n,m,v,(fun i j => (w j).val i),(fun i j => P j i),
    (fun i j => Q j i),hπ,?_,hP,?_⟩
  · have hi := congrArg (Submodule.map K.subtype) hw
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.map_top, Submodule.range_subtype] using hi
  · intro i j
    have he := congrArg (fun x : K => (x : Fin n → B) i) (hQ j)
    change (∑ a, Q j a • w a : K).val i = liftedFreeConnection δ P (w j) i at he
    simp only [liftedFreeConnection, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Submodule.coe_sum, Submodule.coe_smul] at he
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    have he' : δ ((w j).val i) + ∑ a, P a i * (w j).val a =
        ∑ a, (w a).val i * Q j a := by
      simpa only [mul_comm] using he.symm
    exact eq_sub_of_add_eq he'

#print axioms liftedFreeConnection
#print axioms liftedFreeConnectionLinear
#print axioms liftedFreeConnectionLinear_apply
#print axioms liftedFreeConnection_compatible
#print axioms liftedFreeConnection_kernel_stable
#print axioms liftedFreeConnection_leibniz
#print axioms exists_liftedFreeConnection
#print axioms finite_differential_presentation
end StrictEUnit
