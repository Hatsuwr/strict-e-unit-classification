import WholeSystemMomentGauge
import CyclicRegularEulerFrame

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

def wholeMomentMatrix (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam) :
    Matrix (Fin (r+s)) (Fin (r+s)) K :=
  LinearMap.toMatrix' (wholeSystemMomentGauge r s lam hlam).toLinearMap

def wholeMomentInverseMatrix (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam) :
    Matrix (Fin (r+s)) (Fin (r+s)) K :=
  LinearMap.toMatrix' (wholeSystemMomentGauge r s lam hlam).symm.toLinearMap

theorem wholeMomentMatrix_twoSided (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam) :
    wholeMomentMatrix r s lam hlam*wholeMomentInverseMatrix r s lam hlam=1 ∧
    wholeMomentInverseMatrix r s lam hlam*wholeMomentMatrix r s lam hlam=1 := by
  simp only [wholeMomentMatrix,wholeMomentInverseMatrix,← LinearMap.toMatrix'_comp]
  constructor
  · have he : (wholeSystemMomentGauge r s lam hlam).toLinearMap.comp
        (wholeSystemMomentGauge r s lam hlam).symm.toLinearMap=LinearMap.id := by
      apply LinearMap.ext
      intro x
      funext i
      exact congrFun ((wholeSystemMomentGauge r s lam hlam).apply_symm_apply x) i
    rw [he,LinearMap.toMatrix'_id]
  · have he : (wholeSystemMomentGauge r s lam hlam).symm.toLinearMap.comp
        (wholeSystemMomentGauge r s lam hlam).toLinearMap=LinearMap.id := by
      apply LinearMap.ext
      intro x
      funext i
      exact congrFun ((wholeSystemMomentGauge r s lam hlam).symm_apply_apply x) i
    rw [he,LinearMap.toMatrix'_id]

theorem wholeMomentMatrix_action (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam)
    (x : Fin r →K) (h : Fin s →K) :
    (wholeMomentMatrix r s lam hlam).mulVec (finiteParallelVector s x h)=
      finiteParallelVector s x ((forcingMomentMatrix lam).mulVec h) := by
  change Matrix.toLin' (LinearMap.toMatrix' (wholeSystemMomentGauge r s lam hlam).toLinearMap) _=_
  rw [Matrix.toLin'_toMatrix']
  exact wholeSystemMomentGauge_apply r s lam hlam x h

/-- The whole-system moment gauge is constant and hence its regular Euler
connection is exactly conjugation, without an omitted derivative term. -/
theorem wholeMoment_regular_connection (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam)
    (C : Matrix (Fin (r+s)) (Fin (r+s)) (PowerSeries K)) :
    let G := (wholeMomentMatrix r s lam hlam).map (PowerSeries.C K)
    let H := (wholeMomentInverseMatrix r s lam hlam).map (PowerSeries.C K)
    G*H=1 ∧ H*G=1 ∧
      Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*C=(G*C*H)*G := by
  intro G H
  obtain ⟨hGH,hHG⟩ := wholeMomentMatrix_twoSided r s lam hlam
  have hg : G*H=1 := by
    change (PowerSeries.C K).mapMatrix _*(PowerSeries.C K).mapMatrix _=1
    rw [← map_mul,hGH,map_one]
  have hh : H*G=1 := by
    change (PowerSeries.C K).mapMatrix _*(PowerSeries.C K).mapMatrix _=1
    rw [← map_mul,hHG,map_one]
  refine ⟨hg,hh,?_⟩
  have hz : Matrix.of (fun i j =>powerSeriesEuler (G i j))=0 := by
    funext i j
    simp only [G,Matrix.of_apply,Matrix.map_apply,Matrix.zero_apply]
    apply PowerSeries.ext
    intro k
    simp [powerSeriesEuler]
  rw [hz,zero_add,mul_assoc _ H G,hh,mul_one]

/-- A complete frame of the moment-conjugated system transfers back to the
original recursively indexed extension with a proved nonzero determinant. -/
theorem wholeMoment_frame_pullback (r s : ℕ) (lam : Fin s →K) (hlam : Function.Injective lam)
    (C : Matrix (Fin (r+s)) (Fin (r+s)) (PowerSeries K))
    (rho : Fin (r+s) →K)
    (Z : Matrix (Fin (r+s)) (Fin (r+s)) (Polynomial (LaurentSeries K)))
    (hZ : ∀ j i,twistedLogPolynomialEuler (rho j) (Z i j)=
      ∑ l,logPowerSeriesEmbedding
        (((wholeMomentMatrix r s lam hlam).map (PowerSeries.C K)*C*
          (wholeMomentInverseMatrix r s lam hlam).map (PowerSeries.C K)) i l)*Z l j)
    (hdet : Z.det≠0) :
    let Y := ((wholeMomentInverseMatrix r s lam hlam).map (PowerSeries.C K)).map logPowerSeriesEmbedding*Z
    Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
      ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  obtain ⟨hg,hh,hc⟩ := wholeMoment_regular_connection r s lam hlam C
  exact regularEuler_log_frame_pullback C _ _ _ hg hh hc rho Z hZ hdet

end StrictEUnit
end
