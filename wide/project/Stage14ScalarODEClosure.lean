import Stage14FiniteDifferentialClosure

/-!
# Scalar linear ODE closure over a differential scalar field

A nontrivial scalar relation implies finite differential span: zero leading
coefficients are removed, and the nonzero leading coefficient is invertible in
the scalar field. A compatible derivation of that field is essential for span
stability. The conclusion is not an analytic polynomial-coefficient ODE theorem.
-/
noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {k B R : Type*} [CommRing k] [Field B] [CommRing R]
  [Algebra k B] [Algebra k R] [Algebra B R] [IsScalarTower k B R]

/-- Span of exactly the derivatives of orders strictly less than n. -/
def stage14_initialDerivativeSpan (d : Derivation k R R) (f : R) (n : ℕ) :
    Submodule B R :=
  Submodule.span B (Set.range (fun i : Fin n => ((d : R → R)^[i.val]) f))

/-- A recurrence for the next derivative makes the initial derivative span
stable, using the actual scalar derivation and its compatibility. -/
theorem stage14_initialDerivativeSpan_stable
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    (f : R) (n : ℕ)
    (hnext : ((d : R → R)^[n]) f ∈ stage14_initialDerivativeSpan (B := B) d f n) :
    ∀ x ∈ stage14_initialDerivativeSpan (B := B) d f n,
      d x ∈ stage14_initialDerivativeSpan (B := B) d f n := by
  apply differential_span_stable dB d hcompat
  rintro x ⟨i, rfl⟩
  change d (((d : R → R)^[i.val]) f) ∈ _
  rw [← Function.iterate_succ_apply' (d : R → R) i.val f]
  by_cases hi : i.val + 1 < n
  · exact Submodule.subset_span ⟨⟨i.val + 1, hi⟩, rfl⟩
  · have heq : i.val.succ = n := Nat.le_antisymm (Nat.succ_le_of_lt i.isLt) (Nat.le_of_not_gt hi)
    simpa only [heq] using hnext

/-- The zero element has a finite differential span, including the order-zero
case of a nonzero scalar differential relation. -/
theorem stage14_zero_finiteDifferentialSpan (d : Derivation k R R) :
    HasFiniteDifferentialSpan (B := B) d (0 : R) := by
  refine ⟨⊥, Submodule.fg_bot, ?_, Submodule.zero_mem _⟩
  intro x hx
  have hx0 : x = 0 := (Submodule.mem_bot B).mp hx
  simp only [hx0, map_zero, Submodule.zero_mem]

/-- Every genuine scalar linear ODE gives a finite stable derivative span.
No finite-dimensionality or stability assumption is supplied as a hypothesis. -/
theorem scalarLinearDifferentialRelation_finiteSpan
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b))
    {f : R} (hf : HasScalarLinearDifferentialRelation (B := B) d f) :
    HasFiniteDifferentialSpan (B := B) d f := by
  obtain ⟨n, c, hne, heq⟩ := hf
  induction n with
  | zero =>
    have hc : c 0 ≠ 0 := by
      obtain ⟨i, hi⟩ := hne
      simpa only [Fin.eq_zero i] using hi
    have hzero : c 0 • f = 0 := by simpa using heq
    have hfzero : f = 0 := (smul_eq_zero.mp hzero).resolve_left hc
    rw [hfzero]
    exact stage14_zero_finiteDifferentialSpan d
  | succ n ih =>
    by_cases hlast : c (Fin.last (n + 1)) = 0
    · apply ih (fun i => c i.castSucc)
      · obtain ⟨i, hi⟩ := hne
        induction i using Fin.lastCases with
        | last => exact (hi hlast).elim
        | cast i => exact ⟨i, hi⟩
      · simpa only [Fin.sum_univ_castSucc, hlast, zero_smul, add_zero,
          Fin.coe_castSucc] using heq
    · let M : Submodule B R := stage14_initialDerivativeSpan d f (n + 1)
      have hsum : ∑ i : Fin (n + 1), c i.castSucc • ((d : R → R)^[i.val]) f ∈ M := by
        exact Submodule.sum_mem M (fun i _ =>
          M.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩))
      have heq' : (∑ i : Fin (n + 1), c i.castSucc • ((d : R → R)^[i.val]) f) +
          c (Fin.last (n + 1)) • ((d : R → R)^[n + 1]) f = 0 := by
        simpa only [Fin.sum_univ_castSucc, Fin.coe_castSucc, Fin.val_last] using heq
      have hnext : ((d : R → R)^[n + 1]) f ∈ M := by
        apply (M.smul_mem_iff hlast).mp
        rw [eq_neg_of_add_eq_zero_right heq']
        exact M.neg_mem hsum
      exact ⟨M, Submodule.fg_span (Set.finite_range _),
        stage14_initialDerivativeSpan_stable dB d hcompat f (n + 1) hnext,
        Submodule.subset_span ⟨(0 : Fin (n + 1)), rfl⟩⟩

/-- Exact equivalence of a nonzero scalar ODE and finite differential span over
a field whose derivation is compatible with the ambient derivation. -/
theorem scalarLinearDifferentialRelation_iff_finiteSpan
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) (f : R) :
    HasScalarLinearDifferentialRelation (B := B) d f ↔
      HasFiniteDifferentialSpan (B := B) d f :=
  ⟨scalarLinearDifferentialRelation_finiteSpan dB d hcompat,
    finiteDifferentialSpan_has_relation d⟩

/-- Sum closure of genuine scalar linear ODEs over a differential field. -/
theorem scalarLinearDifferentialRelation_add
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) {f g : R}
    (hf : HasScalarLinearDifferentialRelation (B := B) d f)
    (hg : HasScalarLinearDifferentialRelation (B := B) d g) :
    HasScalarLinearDifferentialRelation (B := B) d (f + g) :=
  finiteDifferentialSpan_add_relation d
    (scalarLinearDifferentialRelation_finiteSpan dB d hcompat hf)
    (scalarLinearDifferentialRelation_finiteSpan dB d hcompat hg)

/-- Product closure of genuine scalar linear ODEs over a differential field. -/
theorem scalarLinearDifferentialRelation_mul
    (dB : Derivation k B B) (d : Derivation k R R)
    (hcompat : ∀ b, d (algebraMap B R b) = algebraMap B R (dB b)) {f g : R}
    (hf : HasScalarLinearDifferentialRelation (B := B) d f)
    (hg : HasScalarLinearDifferentialRelation (B := B) d g) :
    HasScalarLinearDifferentialRelation (B := B) d (f * g) :=
  finiteDifferentialSpan_mul_relation d
    (scalarLinearDifferentialRelation_finiteSpan dB d hcompat hf)
    (scalarLinearDifferentialRelation_finiteSpan dB d hcompat hg)

end StrictEUnit
