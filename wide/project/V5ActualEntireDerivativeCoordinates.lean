import EntireSubfieldTaylorEmbedding
import LaurentOrdinaryDerivation

noncomputable section
namespace StrictEUnit

/-- Lightweight actual entire-to-Laurent embedding: no strict arithmetic or
ODE closure stack is needed. -/
def v5ActualEntireLaurentAlgHom (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] LaurentSeries k :=
  { ((HahnSeries.ofPowerSeries ℤ k).comp (subfieldEntireTaylorAlgHom k).toRingHom) with
    commutes' := fun c => by
      change HahnSeries.ofPowerSeries ℤ k
        (subfieldEntireTaylorAlgHom k (algebraMap k (subfieldEntireFunctionAlgebra k) c)) = _
      rw [(subfieldEntireTaylorAlgHom k).commutes]
      rfl }

@[simp] theorem v5_actualEntireLaurent_apply (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    v5ActualEntireLaurentAlgHom k f =
      HahnSeries.ofPowerSeries ℤ k (subfieldEntireTaylorAlgHom k f) := rfl

theorem v5_actualEntireLaurent_injective (k : Subfield ℂ) :
    Function.Injective (v5ActualEntireLaurentAlgHom k) :=
  HahnSeries.ofPowerSeries_injective.comp (subfieldEntireTaylorAlgHom_injective k)

theorem v5_actualEntireLaurent_derivative (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    v5ActualEntireLaurentAlgHom k (subfieldEntireFunctionDerivation k f) =
      laurentOrdinaryDerivation (v5ActualEntireLaurentAlgHom k f) := by
  simp only [v5_actualEntireLaurent_apply, subfieldEntireTaylorAlgHom_derivation,
    laurentOrdinaryDerivation_ofPowerSeries]

theorem v5_actualEntireLaurent_iterate (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ) :
    v5ActualEntireLaurentAlgHom k ((subfieldEntireFunctionDerivation k)^[n] f) =
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[n]
        (v5ActualEntireLaurentAlgHom k f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      v5_actualEntireLaurent_derivative, ih]

/-- Selected derivative coordinates remain actual entire functions in the
same literal coefficient subfield. -/
def v5ActualEntireDerivativeCoordinates {ι : Type*} (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (orders : ι → ℕ) :
    ι → subfieldEntireFunctionAlgebra k :=
  fun i => (subfieldEntireFunctionDerivation k)^[orders i] f

theorem v5_actualEntireDerivativeCoordinates_apply {ι : Type*} (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (orders : ι → ℕ) (i : ι) :
    (v5ActualEntireDerivativeCoordinates k f orders i).val.val =
      iteratedDeriv (orders i) f.val.val :=
  subfieldEntireFunctionDerivation_iterate k f (orders i)

theorem v5_actualEntireDerivativeCoordinates_laurent {ι : Type*} (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (orders : ι → ℕ) (i : ι) :
    v5ActualEntireLaurentAlgHom k (v5ActualEntireDerivativeCoordinates k f orders i) =
      (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[orders i]
        (v5ActualEntireLaurentAlgHom k f) :=
  v5_actualEntireLaurent_iterate k f (orders i)

/-- Retaining derivative order zero retains the original bundled function,
not just an equivalent germ or a scalar multiple. -/
theorem v5_actualEntireDerivativeCoordinates_zero {ι : Type*} (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (orders : ι → ℕ) (i : ι) (hi : orders i = 0) :
    v5ActualEntireDerivativeCoordinates k f orders i = f := by
  simp only [v5ActualEntireDerivativeCoordinates, hi, Function.iterate_zero, id_eq]

/-- One package exposes actual functions, exact formal derivatives, and the
retained original coordinate together. -/
theorem v5_exists_actualEntireDerivativeCoordinates {ι : Type*} (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (orders : ι → ℕ) (i₀ : ι) (hi : orders i₀ = 0) :
    ∃ g : ι → subfieldEntireFunctionAlgebra k, g i₀ = f ∧
      (∀ i, (g i).val.val = iteratedDeriv (orders i) f.val.val) ∧
      ∀ i, v5ActualEntireLaurentAlgHom k (g i) =
        (laurentOrdinaryDerivation : LaurentSeries k → LaurentSeries k)^[orders i]
          (v5ActualEntireLaurentAlgHom k f) :=
  ⟨v5ActualEntireDerivativeCoordinates k f orders,
    v5_actualEntireDerivativeCoordinates_zero k f orders i₀ hi,
    v5_actualEntireDerivativeCoordinates_apply k f orders,
    v5_actualEntireDerivativeCoordinates_laurent k f orders⟩

#print axioms v5_actualEntireLaurent_injective
#print axioms v5_actualEntireLaurent_derivative
#print axioms v5_actualEntireLaurent_iterate
#print axioms v5_actualEntireDerivativeCoordinates_apply
#print axioms v5_actualEntireDerivativeCoordinates_laurent
#print axioms v5_actualEntireDerivativeCoordinates_zero
#print axioms v5_exists_actualEntireDerivativeCoordinates
end StrictEUnit
