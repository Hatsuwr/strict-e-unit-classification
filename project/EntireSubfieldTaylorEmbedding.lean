import EntireTaylorEmbedding

/-! Exact coefficient-field realizations of actual entire functions.
This algebra is defined by membership of all genuine Cauchy coefficients in a
chosen subfield. It is not claimed to be the ring of strict E-functions. -/
noncomputable section
set_option synthInstance.maxHeartbeats 20000
set_option maxHeartbeats 200000
namespace StrictEUnit

/-- Formal series whose actual coefficients belong to a specified subfield. -/
def subfieldPowerSeriesAlgebra (k : Subfield ℂ) : Subalgebra k (PowerSeries ℂ) where
  carrier := {F | ∀ n, PowerSeries.coeff ℂ n F ∈ k}
  zero_mem' := by intro n; simpa using k.zero_mem
  one_mem' := by
    intro n
    rw [PowerSeries.coeff_one]
    split_ifs
    · exact k.one_mem
    · exact k.zero_mem
  add_mem' := by
    intro F G hF hG n
    rw [map_add]
    exact k.add_mem (hF n) (hG n)
  mul_mem' := fun hF hG => powerSeries_coeff_mem_mul k _ _ hF hG
  algebraMap_mem' := by
    intro c n
    rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C]
    split_ifs
    · exact c.property
    · exact k.zero_mem

/-- The exact pullback of the coefficient subalgebra along the genuine Taylor
embedding, with domain still actual entire functions. -/
def subfieldEntireFunctionAlgebra (k : Subfield ℂ) : Subalgebra k entireFunctionAlgebra :=
  (subfieldPowerSeriesAlgebra k).comap (entireTaylorAlgHom.restrictScalars k)

@[simp] theorem mem_subfieldEntireFunctionAlgebra (k : Subfield ℂ)
    (f : entireFunctionAlgebra) :
    f ∈ subfieldEntireFunctionAlgebra k ↔ ∀ n, entireCauchyCoefficient f.val n ∈ k :=
by
  change (∀ n, PowerSeries.coeff ℂ n (entireTaylorAlgHom f) ∈ k) ↔ _
  simp only [coeff_entireTaylorAlgHom]

/-- The actual Cauchy coefficients, now regarded in their specified subfield. -/
def subfieldEntireTaylorSeries (k : Subfield ℂ) (f : subfieldEntireFunctionAlgebra k) :
    PowerSeries k :=
  PowerSeries.mk (fun n => ⟨entireCauchyCoefficient f.val.val n, (mem_subfieldEntireFunctionAlgebra k f.val).mp f.property n⟩)

/-- Mapping the subfield coefficients into ℂ recovers the already constructed
analytic Taylor series, coefficient for coefficient. -/
@[simp] theorem map_subfieldEntireTaylorSeries (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    PowerSeries.map k.subtype (subfieldEntireTaylorSeries k f) =
      entireTaylorAlgHom f.val := by
  ext n
  simp [subfieldEntireTaylorSeries]

/-- A genuine subfield-algebra homomorphism into formal power series over k. -/
def subfieldEntireTaylorAlgHom (k : Subfield ℂ) :
    subfieldEntireFunctionAlgebra k →ₐ[k] PowerSeries k where
  toFun := subfieldEntireTaylorSeries k
  map_zero' := by
    apply PowerSeries.map_injective k.subtype Subtype.val_injective
    rw [map_subfieldEntireTaylorSeries, map_zero]
    exact map_zero entireTaylorAlgHom
  map_one' := by
    apply PowerSeries.map_injective k.subtype Subtype.val_injective
    rw [map_subfieldEntireTaylorSeries, map_one]
    exact map_one entireTaylorAlgHom
  map_add' f g := by
    apply PowerSeries.map_injective k.subtype Subtype.val_injective
    rw [map_subfieldEntireTaylorSeries, map_add,
      map_subfieldEntireTaylorSeries, map_subfieldEntireTaylorSeries]
    exact map_add entireTaylorAlgHom f.val g.val
  map_mul' f g := by
    apply PowerSeries.map_injective k.subtype Subtype.val_injective
    rw [map_subfieldEntireTaylorSeries, map_mul,
      map_subfieldEntireTaylorSeries, map_subfieldEntireTaylorSeries]
    exact map_mul entireTaylorAlgHom f.val g.val
  commutes' c := by
    apply PowerSeries.map_injective k.subtype Subtype.val_injective
    rw [map_subfieldEntireTaylorSeries, PowerSeries.algebraMap_apply, PowerSeries.map_C]
    change entireTaylorAlgHom ((algebraMap k entireFunctionAlgebra) c) = _
    calc
      _ = algebraMap k (PowerSeries ℂ) c :=
        (entireTaylorAlgHom.restrictScalars k).commutes c
      _ = _ := by rw [PowerSeries.algebraMap_apply]; rfl

@[simp] theorem subfieldEntireTaylorAlgHom_apply (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    subfieldEntireTaylorAlgHom k f = subfieldEntireTaylorSeries k f := rfl

@[simp] theorem subfieldEntireTaylorAlgHom_compatibility (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    PowerSeries.map k.subtype (subfieldEntireTaylorAlgHom k f) =
      entireTaylorAlgHom f.val :=
  map_subfieldEntireTaylorSeries k f

theorem subfieldEntireTaylorAlgHom_injective (k : Subfield ℂ) :
    Function.Injective (subfieldEntireTaylorAlgHom k) := by
  intro f g h
  apply Subtype.ext
  apply entireTaylorAlgHom_injective
  have hh := congrArg (PowerSeries.map k.subtype) h
  simpa only [subfieldEntireTaylorAlgHom_compatibility] using hh

/-- A genuine entire derivative still has all coefficients in k. -/
theorem entireFunctionDerivative_mem_subfield (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    entireFunctionDerivative f.val ∈ subfieldEntireFunctionAlgebra k := by
  change ∀ n, PowerSeries.coeff ℂ n
    (entireTaylorAlgHom (entireFunctionDerivative f.val)) ∈ k
  rw [entireTaylorAlgHom_derivative]
  exact powerSeries_coeff_mem_derivative k (entireTaylorAlgHom f.val) f.property

/-- The Taylor image of a generated actual k-algebra is exactly the algebra
generated by the mapped Taylor series. -/
theorem subfieldEntireTaylorAlgHom_adjoin (k : Subfield ℂ)
    (s : Set (subfieldEntireFunctionAlgebra k)) :
    (Algebra.adjoin k s).map (subfieldEntireTaylorAlgHom k) =
      Algebra.adjoin k (subfieldEntireTaylorAlgHom k '' s) :=
  (Algebra.adjoin_image k (subfieldEntireTaylorAlgHom k) s).symm

local instance subfieldEntireBaseModule (k : Subfield ℂ) :
    Module k (subfieldEntireFunctionAlgebra k) :=
  @Algebra.toModule k (subfieldEntireFunctionAlgebra k) inferInstance inferInstance
    (subfieldEntireFunctionAlgebra k).algebra

local instance subfieldEntireSelfModule (k : Subfield ℂ) :
    Module (subfieldEntireFunctionAlgebra k) (subfieldEntireFunctionAlgebra k) :=
  Semiring.toModule

/-- The actual derivative restricted to the exact entire k-coefficient algebra. -/
def subfieldEntireFunctionDerivation (k : Subfield ℂ) :
    Derivation k (subfieldEntireFunctionAlgebra k) (subfieldEntireFunctionAlgebra k) where
  toFun f := ⟨entireFunctionDerivative f.val, entireFunctionDerivative_mem_subfield k f⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add entireFunctionDerivation f.val g.val
  map_smul' c f := by
    apply Subtype.ext
    exact (entireFunctionDerivation.restrictScalars k).map_smul c f.val
  map_one_eq_zero' := by
    apply Subtype.ext
    exact entireFunctionDerivation.map_one_eq_zero
  leibniz' f g := by
    apply Subtype.ext
    exact entireFunctionDerivation.leibniz f.val g.val

@[simp] theorem subfieldEntireFunctionDerivation_apply (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (z : ℂ) :
    (subfieldEntireFunctionDerivation k f).val.val z = deriv f.val.val z := rfl

/-- The k-valued Taylor map commutes with the actual restricted derivative. -/
theorem subfieldEntireTaylorAlgHom_derivation (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) :
    subfieldEntireTaylorAlgHom k (subfieldEntireFunctionDerivation k f) =
      PowerSeries.derivative k (subfieldEntireTaylorAlgHom k f) := by
  have hmap (G : PowerSeries k) :
      PowerSeries.map k.subtype (PowerSeries.derivative k G) =
        PowerSeries.derivative ℂ (PowerSeries.map k.subtype G) := by
    ext n
    simp [PowerSeries.coeff_derivative]
  apply PowerSeries.map_injective k.subtype Subtype.val_injective
  rw [subfieldEntireTaylorAlgHom_compatibility, hmap,
    subfieldEntireTaylorAlgHom_compatibility]
  exact entireTaylorAlgHom_derivative f.val

/-- The identity coordinate belongs to every exact coefficient subfield algebra. -/
def subfieldEntireCoordinate (k : Subfield ℂ) : subfieldEntireFunctionAlgebra k :=
  ⟨entireCoordinate, by
    change ∀ n, PowerSeries.coeff ℂ n (entireTaylorAlgHom entireCoordinate) ∈ k
    rw [entireTaylorAlgHom_coordinate]
    intro n
    rw [PowerSeries.coeff_X]
    split_ifs
    · exact k.one_mem
    · exact k.zero_mem⟩

@[simp] theorem subfieldEntireCoordinate_apply (k : Subfield ℂ) (z : ℂ) :
    (subfieldEntireCoordinate k).val.val z = z := rfl

@[simp] theorem subfieldEntireFunctionDerivation_coordinate (k : Subfield ℂ) :
    subfieldEntireFunctionDerivation k (subfieldEntireCoordinate k) = 1 := by
  apply Subtype.ext
  exact entireFunctionDerivation_coordinate

@[simp] theorem subfieldEntireTaylorAlgHom_coordinate (k : Subfield ℂ) :
    subfieldEntireTaylorAlgHom k (subfieldEntireCoordinate k) = PowerSeries.X := by
  apply PowerSeries.map_injective k.subtype Subtype.val_injective
  rw [subfieldEntireTaylorAlgHom_compatibility, PowerSeries.map_X]
  exact entireTaylorAlgHom_coordinate

/-- Iterating the bundled derivation gives the actual iterated complex derivative. -/
theorem subfieldEntireFunctionDerivation_iterate (k : Subfield ℂ)
    (f : subfieldEntireFunctionAlgebra k) (n : ℕ) :
    ((subfieldEntireFunctionDerivation k)^[n] f).val.val = iteratedDeriv n f.val.val := by
  induction n with
  | zero => simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero]
  | succ n ih =>
    rw [Function.iterate_succ_apply', iteratedDeriv_succ]
    change deriv (((subfieldEntireFunctionDerivation k)^[n] f).val.val) = _
    rw [ih]

end StrictEUnit
