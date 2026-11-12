import OrdinaryPointBasisRangeStability
import LaurentFundamentalSubspaceBasis
import NormalizedChartBasisFactorization

/-!
The same normalized rational chart supplies the scalar extension. Differential
stability, constant straightening, dimension agreement and pivot factorization
are derived in sequence. No second original rational basis is chosen.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- The actual invariant chart factors through W times constant vectors.
The determinant is that of the literal original pivot-row matrix, and its
nonvanishing is derived from the transported basis, not supplied. -/
theorem ordinaryPoint_invariant_chart_fundamental_factorization
    {K : Type*} [Field K] [CharZero K] {r s : ℕ} (β : K)
    (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (W : Matrix (Fin r) (Fin r) (LaurentSeries K))
    (hunit : IsUnit W)
    (hW : ∀ i j, laurentOrdinaryDerivation (W i j) =
      (A.map (ordinaryPointRationalAlgHom β).toRingHom * W) i j)
    (E : Submodule (RatFunc K) (Fin r → RatFunc K))
    (b : Basis (Fin s) (RatFunc K) E) (p : Fin s ↪ Fin r)
    (hpivot : ∀ i j : Fin s, (b j : Fin r → RatFunc K) (p i) =
      if i = j then 1 else 0)
    (hstable : ∀ v : Fin r → RatFunc K, v ∈ E →
      ((fun i => stage14_rationalOrdinaryDerivation (v i)) - A *ᵥ v) ∈ E) :
    let B : Matrix (Fin r) (Fin s) (RatFunc K) :=
      Matrix.of (fun i j => (b j : Fin r → RatFunc K) i)
    ∃ C : Matrix (Fin r) (Fin s) K,
      let V : Matrix (Fin r) (Fin s) (LaurentSeries K) :=
        W * C.map (algebraMap K (LaurentSeries K))
      V = B.map (ordinaryPointRationalAlgHom β).toRingHom * (V.submatrix p id) ∧
        (V.submatrix p id).det ≠ 0 := by
  classical
  let φ : RatFunc K →+* LaurentSeries K := (ordinaryPointRationalAlgHom β).toRingHom
  let B : Matrix (Fin r) (Fin s) (RatFunc K) :=
    Matrix.of (fun i j => (b j : Fin r → RatFunc K) i)
  let EL := normalizedChartScalarExtension φ B
  have hEL : ∀ v : Fin r → LaurentSeries K, v ∈ EL →
      ((fun i => laurentOrdinaryDerivation (v i)) - A.map φ *ᵥ v) ∈ EL := by
    simpa only [normalizedChartScalarExtension] using
      ordinaryPoint_basis_range_covariant_stable β A E b hstable
  obtain ⟨hmap, t, ht, hdim, v0, v, hc, hv⟩ :=
    laurent_covariant_subspace_fundamental_constant_basis (A.map φ) W hW hunit EL hEL
  have hts : t = s := normalizedChartScalarExtension_basis_card φ B p hpivot v
  let e : Fin t ≃ Fin s := finCongr hts
  let v' : Basis (Fin s) (LaurentSeries K) EL := v.reindex e
  let C : Matrix (Fin r) (Fin s) K := Matrix.of (fun i j =>
    (((v0 (e.symm j) : Fin r → LaurentSeries K) i).coeff 0))
  let V : Matrix (Fin r) (Fin s) (LaurentSeries K) :=
    Matrix.of (fun i j => (v' j : Fin r → LaurentSeries K) i)
  have hV : V = W * C.map (algebraMap K (LaurentSeries K)) := by
    apply Matrix.ext
    intro i j
    change (((v.reindex e) j : Fin r → LaurentSeries K) i) = _
    rw [Basis.reindex_apply]
    exact congrFun (hv (e.symm j)) i
  have hf := normalizedChartScalarExtension_basis_factorization φ B p hpivot v'
  change V = B.map φ * (V.submatrix p id) ∧ (V.submatrix p id).det ≠ 0 at hf
  rw [hV] at hf
  exact ⟨C, hf⟩

end StrictEUnit
end
