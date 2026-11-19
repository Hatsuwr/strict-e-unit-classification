import OrdinaryPointMatrixSystem
import Mathlib.Data.Matrix.Basic

/-!
Map the once-constructed ordinary-point formal fundamental matrix into the
actual Laurent field. All differentiation uses the actual coefficientwise
embedding compatibility. No new fundamental matrix premise is supplied.
-/
noncomputable section
open scoped Matrix
namespace StrictEUnit

/-- For one fixed rational A, choose an ordinary point and a unit Laurent
fundamental matrix once. The coefficient embedding is the original translated
rational AlgHom, and the equation is the genuine left matrix equation. -/
theorem exists_ordinaryPoint_laurent_fundamentalMatrix
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) (RatFunc K)) :
    ∃ β : K, ∃ W : Matrix (Fin r) (Fin r) (LaurentSeries K), IsUnit W ∧
      ∀ i j, laurentOrdinaryDerivation (W i j) =
        (A.map (ordinaryPointRationalAlgHom β).toRingHom * W) i j := by
  classical
  obtain ⟨T, hT, U, hU, β, hβ, B, Z, hB, hZ0, hZder, hZunit⟩ :=
    exists_ordinaryPoint_formalFundamentalMatrix A
  let ψ : PowerSeries K →+* LaurentSeries K := HahnSeries.ofPowerSeries ℤ K
  have hBmap : B.map ψ = A.map (ordinaryPointRationalAlgHom β).toRingHom := by
    apply Matrix.ext
    intro i j
    exact hB i j
  refine ⟨β, Z.map ψ, ?_, ?_⟩
  · exact hZunit.map ψ.mapMatrix
  · intro i j
    have hij := congrArg (fun M : Matrix (Fin r) (Fin r) (PowerSeries K) => M i j) hZder
    change PowerSeries.derivative K (Z i j) = (B*Z) i j at hij
    change laurentOrdinaryDerivation (ψ (Z i j)) =
      (A.map (ordinaryPointRationalAlgHom β).toRingHom * Z.map ψ) i j
    calc
      _ = ψ (PowerSeries.derivative K (Z i j)) :=
        laurentOrdinaryDerivation_ofPowerSeries (Z i j)
      _ = ψ ((B*Z) i j) := congrArg ψ hij
      _ = (B.map ψ * Z.map ψ) i j := RingHom.map_matrix_mul B Z i j ψ
      _ = _ := by rw [hBmap]

end StrictEUnit
end
