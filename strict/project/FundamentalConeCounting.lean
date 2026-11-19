import BinomialNaturalScaling
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
import Mathlib.Algebra.Module.ZLattice.Covolume

noncomputable section
open scoped Topology
open Filter MeasureTheory NumberField
namespace StrictEUnit

/-- Actual fundamental-cone lattice points have linear norm-count asymptotics.
This is a geometric input toward ideal counting, not a prime-density theorem. -/
theorem fundamentalCone_lattice_count_limit
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, Tendsto (fun c : ℝ =>
      (Nat.card ({x : mixedEmbedding.euclidean.mixedSpace K |
        mixedEmbedding.euclidean.toMixed K x ∈ mixedEmbedding.fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding.euclidean.toMixed K x) ≤ c} ∩
        mixedEmbedding.euclidean.integerLattice K :
          Set (mixedEmbedding.euclidean.mixedSpace K)) : ℝ) / c)
      atTop (𝓝 C) := by
  classical
  let e := mixedEmbedding.euclidean.toMixed K
  let X : Set (mixedEmbedding.euclidean.mixedSpace K) :=
    e ⁻¹' mixedEmbedding.fundamentalCone K
  let F : mixedEmbedding.euclidean.mixedSpace K → ℝ :=
    fun x => mixedEmbedding.norm (e x)
  have hs : {x ∈ X | F x ≤ 1} = e ⁻¹' mixedEmbedding.fundamentalCone.normLeOne K := rfl
  have hX : ∀ ⦃x⦄ ⦃r : ℝ⦄, x ∈ X → 0 < r → r • x ∈ X := by
    intro x r hx hr
    change e (r • x) ∈ mixedEmbedding.fundamentalCone K
    rw [map_smul]
    exact mixedEmbedding.fundamentalCone.smul_mem_of_mem hx (ne_of_gt hr)
  have hF : ∀ x ⦃r : ℝ⦄, 0 ≤ r →
      F (r • x) = r ^ Module.finrank ℝ (mixedEmbedding.euclidean.mixedSpace K) * F x := by
    intro x r hr
    dsimp [F]
    rw [map_smul, mixedEmbedding.norm_smul, abs_of_nonneg hr,
      mixedEmbedding.euclidean.finrank]
  have hbounded : Bornology.IsBounded {x ∈ X | F x ≤ 1} := by
    rw [hs, ← e.image_symm_eq_preimage]
    exact e.symm.lipschitz.isBounded_image (mixedEmbedding.fundamentalCone.isBounded_normLeOne K)
  have hmeas : MeasurableSet {x ∈ X | F x ≤ 1} := by
    rw [hs]
    exact (mixedEmbedding.fundamentalCone.measurableSet_normLeOne K).preimage e.continuous.measurable
  have hfront : volume (frontier {x ∈ X | F x ≤ 1}) = 0 := by
    rw [hs]
    have hf := e.toHomeomorph.preimage_frontier (mixedEmbedding.fundamentalCone.normLeOne K)
    change volume (frontier (e.toHomeomorph ⁻¹' mixedEmbedding.fundamentalCone.normLeOne K)) = 0
    rw [← hf]
    exact ((mixedEmbedding.euclidean.volumePreserving_toMixed K).measure_preimage
      (s := frontier (mixedEmbedding.fundamentalCone.normLeOne K))
      isClosed_frontier.measurableSet.nullMeasurableSet).trans
        (mixedEmbedding.fundamentalCone.volume_frontier_normLeOne K)
  exact ⟨_, ZLattice.covolume.tendsto_card_le_div'
    (mixedEmbedding.euclidean.integerLattice K) hX hF hbounded hmeas hfront⟩

/-- In particular the actual cone count is eventually bounded by a linear
function of the norm cutoff. -/
theorem fundamentalCone_lattice_count_linear_bound
    (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ᶠ c : ℝ in atTop,
      (Nat.card ({x : mixedEmbedding.euclidean.mixedSpace K |
        mixedEmbedding.euclidean.toMixed K x ∈ mixedEmbedding.fundamentalCone K ∧
        mixedEmbedding.norm (mixedEmbedding.euclidean.toMixed K x) ≤ c} ∩
        mixedEmbedding.euclidean.integerLattice K :
          Set (mixedEmbedding.euclidean.mixedSpace K)) : ℝ) ≤ C * c := by
  obtain ⟨C, hC⟩ := fundamentalCone_lattice_count_limit K
  refine ⟨C + 1, ?_⟩
  filter_upwards [hC.eventually (eventually_lt_nhds (lt_add_one C)),
    eventually_gt_atTop (0 : ℝ)] with c hc hpos
  exact (div_le_iff₀ hpos).mp hc.le

end StrictEUnit
end
