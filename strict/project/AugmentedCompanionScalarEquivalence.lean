import ForcedCompanionJetEquivalence
import FiniteForcingSolutionReconstruction

noncomputable section
open scoped BigOperators Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

/-- The explicit lift of f uses its actual source residual as forcing, never
an independently chosen polynomial. -/
def augmentedSourceJet (n : ℕ) (c : Fin (n+1) → LaurentSeries K)
    (t f : LaurentSeries K) (d : ℕ) : Fin (((n+1)+1)+d) → LaurentSeries K :=
  polynomialForcingJet (sourceCompanionResidual n c t f) (sourceOrdinaryDerivativeJet n f) d

/-- The concrete augmented matrix has exactly the scalar equation D^(d+1)Qf=0
on its canonical lift, with Q the original cleared companion residual. -/
theorem augmentedCompanion_scalar_lift_iff (n : ℕ) (c : Fin (n+1) → LaurentSeries K)
    (t f : LaurentSeries K) (ht : t≠0) (d : ℕ) :
    (∀ i,stage14_laurentAlgebraDerivation (augmentedSourceJet n c t f d i)=
      ∑ j,polynomialForcingConnection (minimalDerivativeCompanion (n+1) c)
        (fun i =>if i.val+1=n+1 then t⁻¹ else 0) d i j*augmentedSourceJet n c t f d j) ↔
    (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1]
      (sourceCompanionResidual n c t f)=0 := by
  unfold augmentedSourceJet
  rw [polynomialForcingJet_solution_iff,sourceCompanion_jet_solution_iff n c t f _ ht]
  simp only [and_true]

/-- No additional matrix solutions are hidden: EVERY solution is the
canonical lift of a scalar solution, and conversely. -/
theorem augmentedCompanion_all_solutions_iff (n : ℕ) (c : Fin (n+1) → LaurentSeries K)
    (t : LaurentSeries K) (ht : t≠0) (d : ℕ)
    (v : Fin (((n+1)+1)+d) → LaurentSeries K) :
    (∀ i,stage14_laurentAlgebraDerivation (v i)=
      ∑ j,polynomialForcingConnection (minimalDerivativeCompanion (n+1) c)
        (fun i =>if i.val+1=n+1 then t⁻¹ else 0) d i j*v j) ↔
    ∃ f,v=augmentedSourceJet n c t f d ∧
      (stage14_laurentAlgebraDerivation (k:=K) : LaurentSeries K → LaurentSeries K)^[d+1]
        (sourceCompanionResidual n c t f)=0 := by
  constructor
  · intro hv
    obtain ⟨P,y,hvjet,hP,hy⟩ := (polynomialForcing_solution_iff_exists_jet _ _ d v).mp hv
    obtain ⟨f,hyjet,hf⟩ := (sourceCompanion_solution_iff_exists_jet n c y t P ht).mp hy
    refine ⟨f,?_,?_⟩
    · simpa only [augmentedSourceJet,hyjet,← hf] using hvjet
    · simpa only [hf] using hP
  · rintro ⟨f,rfl,hf⟩
    exact (augmentedCompanion_scalar_lift_iff n c t f ht d).mpr hf

end StrictEUnit
end
