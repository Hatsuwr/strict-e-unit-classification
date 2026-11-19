import EntireSubfieldTaylorEmbedding
import V5MeromorphicZero

noncomputable section
namespace StrictEUnit

/-- Meromorphic functions at the deleted origin, with a genuine entire
pole-clearing numerator whose Taylor coefficients lie in k. -/
def V5ArithmeticMeromorphicZero (k : Subfield ℂ) (u : ℂˣ → ℂ) : Prop :=
  ∃ (n : ℕ) (F : subfieldEntireFunctionAlgebra k), ∀ z : ℂˣ,
    F.val.val z = (z : ℂ)^n * u z

theorem v5_arithmetic_power_clear {k : Subfield ℂ} {u : ℂˣ → ℂ}
    {n : ℕ} {F : subfieldEntireFunctionAlgebra k}
    (hF : ∀ z : ℂˣ, F.val.val z = (z : ℂ)^n * u z) (r : ℕ) :
    ∃ G : subfieldEntireFunctionAlgebra k, ∀ z : ℂˣ, G.val.val z = (z : ℂ)^(n+r)*u z := by
  refine ⟨(subfieldEntireCoordinate k)^r * F, ?_⟩
  intro z
  change (z : ℂ)^r * F.val.val z = _
  rw [hF,pow_add]
  ring

theorem V5ArithmeticMeromorphicZero.of_entire {k : Subfield ℂ} (F : subfieldEntireFunctionAlgebra k) :
    V5ArithmeticMeromorphicZero k (fun z => F.val.val z) :=
  ⟨0, F, fun z => by rw [pow_zero,one_mul]⟩

theorem V5ArithmeticMeromorphicZero.add {k : Subfield ℂ} {u v : ℂˣ → ℂ}
    (hu : V5ArithmeticMeromorphicZero k u) (hv : V5ArithmeticMeromorphicZero k v) :
    V5ArithmeticMeromorphicZero k (u+v) := by
  obtain ⟨n,F,hF⟩ := hu
  obtain ⟨m,G,hG⟩ := hv
  obtain ⟨F',hF'⟩ := v5_arithmetic_power_clear hF m
  obtain ⟨G',hG'⟩ := v5_arithmetic_power_clear hG n
  refine ⟨n+m,F'+G',fun z => ?_⟩
  change F'.val.val z + G'.val.val z = (z : ℂ)^(n+m)*(u z+v z)
  rw [hF',hG', Nat.add_comm m n, mul_add]

theorem V5ArithmeticMeromorphicZero.mul {k : Subfield ℂ} {u v : ℂˣ → ℂ}
    (hu : V5ArithmeticMeromorphicZero k u) (hv : V5ArithmeticMeromorphicZero k v) :
    V5ArithmeticMeromorphicZero k (u*v) := by
  obtain ⟨n,F,hF⟩ := hu
  obtain ⟨m,G,hG⟩ := hv
  refine ⟨n+m,F*G,fun z => ?_⟩
  change F.val.val z * G.val.val z = (z : ℂ)^(n+m)*(u z*v z)
  rw [hF,hG,pow_add]
  ring

/-- Recover the required scalar from one Taylor coefficient of a
pole-clearing numerator. No assumptions on the other coefficients of W. -/
theorem v5_arithmetic_normalized_value {k : Subfield ℂ} {u : ℂˣ → ℂ}
    (hu : V5ArithmeticMeromorphicZero k u) {m : ℤ} (W : entireFunctionAlgebra)
    (hW : ∀ z : ℂˣ, u z = (z : ℂ)^m * W.val z) : W.val 0 ∈ k := by
  obtain ⟨n,F,hF⟩ := hu
  obtain ⟨G,hG⟩ := v5_arithmetic_power_clear hF m.natAbs
  let N := n + m.natAbs
  have hnonneg : 0 ≤ (N : ℤ) + m := by
    dsimp [N]
    cases m with
    | ofNat a => simp; omega
    | negSucc a => simp; omega
  let d := ((N : ℤ) + m).toNat
  have hd : (d : ℤ) = (N : ℤ) + m := Int.toNat_of_nonneg hnonneg
  have hprod : G.val = entireCoordinate^d * W := by
    apply Subtype.ext
    funext z
    let C := {z : ℂ | G.val.val z = (entireCoordinate^d * W : entireFunctionAlgebra).val z}
    have hc : IsClosed C := isClosed_eq G.val.property.continuous
      (entireCoordinate^d * W : entireFunctionAlgebra).property.continuous
    have he : ({0}ᶜ : Set ℂ) ⊆ C := by
      intro z hz
      have hz' : z ≠ 0 := by simpa using hz
      let e := Units.mk0 z hz'
      change G.val.val e = (e : ℂ)^d * W.val e
      rw [hG e,hW e]
      rw [← mul_assoc, ← zpow_natCast (e : ℂ) N, ← zpow_add₀ (Units.ne_zero e), ← hd, zpow_natCast]
    have ha := closure_minimal he hc
    rw [(dense_compl_singleton (0 : ℂ)).closure_eq] at ha
    exact ha (Set.mem_univ z)
  have hc := (mem_subfieldEntireFunctionAlgebra k G.val).mp G.property d
  rw [← coeff_entireTaylorAlgHom, hprod] at hc
  simp only [map_mul, map_pow, entireTaylorAlgHom_coordinate] at hc
  have hcoef := PowerSeries.coeff_X_pow_mul (entireTaylorAlgHom W) d 0
  simp only [Nat.zero_add] at hcoef
  rw [hcoef, coeff_entireTaylorAlgHom, entireCauchyCoefficient_zero W.property] at hc
  exact hc

end StrictEUnit
#print axioms StrictEUnit.v5_arithmetic_power_clear
#print axioms StrictEUnit.V5ArithmeticMeromorphicZero.add
#print axioms StrictEUnit.V5ArithmeticMeromorphicZero.mul
#print axioms StrictEUnit.v5_arithmetic_normalized_value
