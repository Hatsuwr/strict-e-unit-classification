import LaurentFundamentalComap
import LaurentStableSubspaceDescent
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
Constant-basis descent followed by transport through the SAME unit W.
No rational base change, Picard-Vessiot premise or rank estimate is used.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- An invariant E has a basis of W times literal constant vectors. The
preimage basis b0 belongs to the actual comap, and each constant is precisely
its original zeroth Laurent coefficient. Both bases and their size are derived.
Only the transport step needs W to be a unit. -/
theorem laurent_covariant_subspace_fundamental_constant_basis
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A W : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (hW : ∀ i j, laurentOrdinaryDerivation (W i j) = (A*W) i j)
    (hunit : IsUnit W)
    (E : Submodule (LaurentSeries K) (Fin r → LaurentSeries K))
    (hstable : ∀ v : Fin r → LaurentSeries K, v ∈ E →
      ((fun i => laurentOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E) :
    (E.comap (Matrix.toLin' W)).map (Matrix.toLin' W) = E ∧
      ∃ s : ℕ, s ≤ r ∧ s = Module.finrank (LaurentSeries K) E ∧
        ∃ b0 : Basis (Fin s) (LaurentSeries K) (E.comap (Matrix.toLin' W)),
          ∃ b : Basis (Fin s) (LaurentSeries K) E,
            (∀ i : Fin s, ∀ j : Fin r,
              (b0 i : Fin r → LaurentSeries K) j =
                algebraMap K (LaurentSeries K)
                  (((b0 i : Fin r → LaurentSeries K) j).coeff 0)) ∧
            (∀ i : Fin s, (b i : Fin r → LaurentSeries K) =
              W *ᵥ (fun j => algebraMap K (LaurentSeries K)
                (((b0 i : Fin r → LaurentSeries K) j).coeff 0))) := by
  classical
  have hinj : Function.Injective (Matrix.toLin' W) := by
    change Function.Injective W.mulVec
    exact (Matrix.mulVec_injective_iff_isUnit (A := W)).mpr hunit
  have hsurj : Function.Surjective (Matrix.toLin' W) := by
    change Function.Surjective W.mulVec
    exact (Matrix.mulVec_surjective_iff_isUnit (A := W)).mpr hunit
  have hmap : (E.comap (Matrix.toLin' W)).map (Matrix.toLin' W) = E :=
    Submodule.map_comap_eq_of_surjective hsurj E
  have hle : E ≤ LinearMap.range (Matrix.toLin' W) := by
    intro v hv
    exact (LinearMap.mem_range).mpr (hsurj v)
  let e : E.comap (Matrix.toLin' W) ≃ₗ[LaurentSeries K] E :=
    Submodule.comap_equiv_self_of_inj_of_le hinj hle
  obtain ⟨s, hs, hdim0, p, b0, hc, hpivot, hspan⟩ :=
    laurent_stable_subspace_constant_basis (E.comap (Matrix.toLin' W))
      (laurent_fundamental_comap_derivative_stable A W hW E hstable)
  let b : Basis (Fin s) (LaurentSeries K) E := b0.map e
  have hdim : s = Module.finrank (LaurentSeries K) E := by
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b).symm
  have hb (i : Fin s) : (b i : Fin r → LaurentSeries K) =
      W *ᵥ (b0 i : Fin r → LaurentSeries K) := by
    change (((b0.map e) i : E) : Fin r → LaurentSeries K) = _
    rw [Basis.map_apply]
    rfl
  refine ⟨hmap, s, hs, hdim, b0, b, hc, ?_⟩
  intro i
  rw [hb]
  apply congrArg W.mulVec
  funext j
  exact hc i j

end StrictEUnit
end
