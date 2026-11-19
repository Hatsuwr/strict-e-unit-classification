import PrescribedRegularCyclicRow
import OrdinaryBorelMinimalCyclic
import RationalRelationKernelSpan
import PolynomialRelationSpecialization

/-! At the specified ordinary point, the prescribed row either lifts to an
actual polynomial relation or constructs a regular minimal scalar recurrence.
The input Laurent family and its given connection matrix remain unchanged. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 20000
open scoped BigOperators
namespace StrictEUnit

theorem ordinaryLaurent_minimalCyclicData_of_prefix
    {K : Type*} [Field K] (g : LaurentSeries K) (m : ℕ) (b : Fin m → RatFunc K)
    (hli : LinearIndependent (RatFunc K) (fun i : Fin m =>
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] g))
    (hrec : (∑ i, b i • (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] g) =
      (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[m] g) :
    OrdinaryBorelMinimalCyclicData g m b := by
  letI : SMul K (LaurentSeries K) := Algebra.toSMul
  letI : SMul K (RatFunc K) := Algebra.toSMul
  letI : Module K (LaurentSeries K) := Algebra.toModule
  letI : Module K (RatFunc K) := Algebra.toModule
  letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
  have hnext : (stage14_laurentAlgebraDerivation (k := K) : LaurentSeries K → LaurentSeries K)^[m] g ∈
      stage14_initialDerivativeSpan (B := RatFunc K) stage14_laurentAlgebraDerivation g m := by
    change (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[m] g ∈
      Submodule.span (RatFunc K) (Set.range (fun i : Fin m =>
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[i.val] g))
    rw [← hrec]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨hli, hrec, ?_, ?_, ?_⟩
  · intro b' hb'
    apply hli.fintypeLinearCombination_injective
    exact hb'.trans hrec.symm
  · exact stage14_initialDerivativeSpan_stable stage14_rationalOrdinaryDerivation
      stage14_laurentAlgebraDerivation (fun q => stage14_rationalLaurent_differential q) g m hnext
  · exact minimalDerivativeCompanion_rows stage14_laurentAlgebraDerivation g m b hrec

theorem ordinary_relation_or_prescribed_regular_minimal
    {K : Type*} [Field K] [CharZero K] {r : ℕ}
    (α : K) (Y : Fin r → LaurentSeries K)
    (A : Fin r → Fin r → RatFunc K)
    (hY : ∀ i, laurentOrdinaryDerivation (Y i) = ∑ j, A i j • Y j)
    (t : Polynomial K) (U : Fin r → Fin r → Polynomial K)
    (hα : t.eval α ≠ 0)
    (hclear : ∀ i j, algebraMap (Polynomial K) (RatFunc K) (U i j) =
      algebraMap (Polynomial K) (RatFunc K) t * A i j)
    (c : Fin r → K) :
    (∃ p : Fin r → Polynomial K,
      p ∈ LinearMap.ker (formalPolynomialRelationMap Y) ∧ ∀ j, (p j).eval α = c j) ∨
    (∃ m : ℕ, 0 < m ∧ m ≤ r ∧ ∃ p : Fin r → Polynomial K,
      (∀ j, (p j).eval α = c j) ∧ ∃ b : Fin m → RatFunc K,
        OrdinaryBorelMinimalCyclicData
          (∑ j, algebraMap (Polynomial K) (RatFunc K) (p j) • Y j) m b ∧
        ∀ i, ∃ bS : PowerSeries K,
          HahnSeries.ofPowerSeries ℤ K bS = ordinaryPointRationalMap α (b i)) := by
  classical
  obtain ⟨s, B, hB⟩ := formalPolynomialRelation_specialization_basis Y
  by_cases hc : c ∈ Submodule.span K (Set.range (fun i j => ((B i).val j).eval α))
  · exact Or.inl (polynomial_relation_of_specialized_span (formalPolynomialRelationMap Y) B α c hc)
  · have hker := formalRationalRelationKernel_span_basis Y s B
    obtain ⟨m, hm, hdim, p, hp, hli, b, bS, hrec, hbreg⟩ :=
      exists_prescribed_polynomial_regular_cyclic_row α
        (Fintype.linearCombination (RatFunc K) Y) A t U hα hclear
        (fun i => (B i).val) hker (hB α) c hc
    letI : SMul K (LaurentSeries K) := Algebra.toSMul
    letI : SMul K (RatFunc K) := Algebra.toSMul
    letI : Module K (LaurentSeries K) := Algebra.toModule
    letI : Module K (RatFunc K) := Algebra.toModule
    letI : IsScalarTower K (RatFunc K) (LaurentSeries K) := stage14_rationalLaurentScalarTower
    have he (n : ℕ) :
        (Fintype.linearCombination (RatFunc K) Y)
          ((rationalCovariantRow stage14_rationalOrdinaryDerivation A)^[n]
            (fun j => algebraMap (Polynomial K) (RatFunc K) (p j))) =
        (laurentOrdinaryDerivation : LaurentSeries K → LaurentSeries K)^[n]
          (∑ j, algebraMap (Polynomial K) (RatFunc K) (p j) • Y j) := by
      exact (rationalCovariantRow_iterate_eval stage14_rationalOrdinaryDerivation
        stage14_laurentAlgebraDerivation (fun q => stage14_rationalLaurent_differential q)
        A Y hY _ n).symm
    simp_rw [he] at hli hrec
    exact Or.inr ⟨m, hm, by omega, p, hp, b,
      ordinaryLaurent_minimalCyclicData_of_prefix _ m b hli hrec,
      fun i => ⟨bS i, hbreg i⟩⟩
end StrictEUnit
