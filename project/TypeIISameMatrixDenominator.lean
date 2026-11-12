import TypeIICommonIntegralMatrix
import TypeIIIntegralLiftIdentity
import TypeIIIntegralLiftDeterminant
import CommonMatrixNormDenominator
import PolynomialIntegralCommonNormHouse

/-! Exact simultaneous denominator composition. Every connection polynomial
and every matrix column is the actual same-data construction. Only the
nonzero determinant coefficient, not any representatives, remains supplied. -/
noncomputable section
open scoped BigOperators NumberField Matrix
namespace StrictEUnit

/-- The same literal lift matrix has integral products with every actual
polynomial H_n through the finite cutoff. Rational equality is reflected
through the injective polynomial embedding; polynomiality is not assumed. -/
theorem typeII_explicit_lift_common_polynomial_products
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T Q : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → 𝓞 K) (δ : K)
    (N M τ s : ℕ)
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → (b i n : K) = δ * PowerSeries.coeff K n (f i))
    (hcut : (s+r-1)*(τ+1) ≤ M) :
    ∀ n, n ≤ s → ∃ B : Matrix (Fin r) (Fin r) (Polynomial (𝓞 K)),
      dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n *
        (Polynomial.mapRingHom (algebraMap (𝓞 K) K)).mapMatrix
          (typeIIIntegralLiftMatrix r N τ T Q b) =
        (Polynomial.mapRingHom (algebraMap (𝓞 K) K)).mapMatrix B := by
  classical
  let φ : 𝓞 K →+* K := algebraMap (𝓞 K) K
  let ψ : Polynomial K →+* RatFunc K := algebraMap (Polynomial K) (RatFunc K)
  letI : CharZero (RatFunc K) := ⟨by
    intro a b h
    apply Nat.cast_injective (R := K)
    apply (algebraMap K (RatFunc K)).injective
    simpa only [map_natCast] using h⟩
  obtain ⟨Z,hZ,hdual,hproducts⟩ := exists_typeII_common_integral_matrix φ T Q U P A
    f b δ N M τ s hT0 hT hU hP hclear hf hcontact hb hcut
  have hfirst (i j : Fin r) : Z j.val i = typeIIIntegralLiftMatrix r N τ T Q b i j := by
    have hj : j.val ≤ s+r-1 := by omega
    have hc : j.val*(τ+1) ≤ M := (Nat.mul_le_mul_right (τ+1) hj).trans hcut
    apply Polynomial.map_injective φ NumberField.RingOfIntegers.coe_injective
    exact (hZ j.val hj i).trans
      (typeIIIntegralLift_map_column φ T Q U P f b δ N M τ j.val
        hT hU hP hf hcontact hb hc i).symm
  intro n hn
  obtain ⟨B,hB⟩ := hproducts n hn
  refine ⟨B, ?_⟩
  apply Matrix.map_injective (RatFunc.algebraMap_injective (K := K))
  change ψ.mapMatrix (dividedPolynomialConnectionSequence (T.map φ) U n *
    (Polynomial.mapRingHom φ).mapMatrix (typeIIIntegralLiftMatrix r N τ T Q b)) =
      ψ.mapMatrix ((Polynomial.mapRingHom φ).mapMatrix B)
  rw [map_mul]
  have hH : ψ.mapMatrix (dividedPolynomialConnectionSequence (T.map φ) U n) =
      Matrix.of (fun i l : Fin r => (typeIIRationalPolynomialMap φ T)^n *
        matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i l /
          (n.factorial : RatFunc K)) := by
    apply Matrix.ext
    intro i l
    change ψ (dividedPolynomialConnectionSequence (T.map φ) U n i l) =
      (typeIIRationalPolynomialMap φ T)^n *
        matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i l /
          (n.factorial : RatFunc K)
    rw [dividedPolynomialConnectionSequence_map stage14_rationalOrdinaryDerivation ψ
      (fun p => stage14_rationalOrdinaryDerivation_polynomial p) (T.map φ) U A hclear n i l]
    change (n.factorial : RatFunc K)⁻¹ * (typeIIRationalPolynomialMap φ T)^n *
      matrixConnectionSequence stage14_rationalOrdinaryDerivation A n i l = _
    ring
  rw [hH]
  have hM : ψ.mapMatrix ((Polynomial.mapRingHom φ).mapMatrix
        (typeIIIntegralLiftMatrix r N τ T Q b)) =
      Matrix.of (fun l j : Fin r => typeIIRationalPolynomialMap φ (Z j.val l)) := by
    apply Matrix.ext
    intro i j
    change ψ ((typeIIIntegralLiftMatrix r N τ T Q b i j).map φ) =
      typeIIRationalPolynomialMap φ (Z j.val i)
    rw [hfirst i j]
    rfl
  rw [hM]
  exact hB

/-- ONE positive integer, the norm of ONE coefficient of the SAME determinant,
clears every coefficient of all H_n for n≤s and has an explicit House bound.
The determinant coefficient nonvanishing is the remaining rank hypothesis. -/
theorem typeII_same_matrix_positive_denominator
    {K : Type*} [Field K] [NumberField K] {r : ℕ}
    (T Q : Polynomial (𝓞 K)) (U : Matrix (Fin r) (Fin r) (Polynomial K))
    (P : Fin r → Polynomial K) (A : Matrix (Fin r) (Fin r) (RatFunc K))
    (f : Fin r → PowerSeries K) (b : Fin r → ℕ → 𝓞 K) (δ : K)
    (N M τ s : ℕ)
    (hT0 : typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T ≠ 0)
    (hT : (T.map (algebraMap (𝓞 K) K)).natDegree ≤ τ)
    (hU : ∀ i l, (U i l).natDegree ≤ τ)
    (hP : ∀ i, (P i).natDegree ≤ N)
    (hclear : ∀ i l, algebraMap (Polynomial K) (RatFunc K) (U i l) =
      typeIIRationalPolynomialMap (algebraMap (𝓞 K) K) T * A i l)
    (hf : ∀ i, (T.map (algebraMap (𝓞 K) K) : PowerSeries K)*PowerSeries.derivative K (f i) =
      ∑ l, (U i l : PowerSeries K)*f l)
    (hcontact : ∀ i, seriesContact (N+M+1)
      ((Q.map (algebraMap (𝓞 K) K) : PowerSeries K)*f i-(P i : PowerSeries K)))
    (hb : ∀ i n, n ≤ N+M → (b i n : K) = δ * PowerSeries.coeff K n (f i))
    (hcut : (s+r-1)*(τ+1) ≤ M)
    (e : ℕ) (hTe : T.natDegree ≤ e) (hQN : Q.natDegree ≤ N)
    (HT HQ Hb : ℝ) (hHT : 0 ≤ HT) (hHQ : 0 ≤ HQ) (hHb : 0 ≤ Hb)
    (hTH : ∀ n, NumberField.house (T.coeff n : K) ≤ HT)
    (hQH : ∀ n, NumberField.house (Q.coeff n : K) ≤ HQ)
    (hbH : ∀ i n, n ≤ N+M → NumberField.house (b i n : K) ≤ Hb)
    (k : ℕ) (hk : (typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k ≠ 0) :
    let q := Int.natAbs (Algebra.norm ℤ ((typeIIIntegralLiftMatrix r N τ T Q b).det.coeff k))
    0 < q ∧
    (q : ℝ) ≤ ((r.factorial : ℝ)*(((N+(r-1)*τ : ℕ)+1 : ℝ)*
      typeIIIntegralLiftMatrixBound r e N HT HQ Hb)^r)^Module.finrank ℚ K ∧
    ∀ n, n ≤ s → ∀ i j : Fin r, ∀ l : ℕ,
      IsIntegral ℤ ((q : K)*
        (dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n i j).coeff l) := by
  classical
  let φ : Polynomial (𝓞 K) →+* Polynomial K := Polynomial.mapRingHom (algebraMap (𝓞 K) K)
  let C := typeIIIntegralLiftMatrix r N τ T Q b
  let H := fun n => dividedPolynomialConnectionSequence (T.map (algebraMap (𝓞 K) K)) U n
  have hp := typeII_explicit_lift_common_polynomial_products T Q U P A f b δ N M τ s
    hT0 hT hU hP hclear hf hcontact hb hcut
  choose B hB using fun n : Fin (s+1) => hp n.val (by omega)
  have hprod (x : Fin (s+1) × Fin r × Fin r) (l : ℕ) :
      IsIntegral ℤ ((C.det.map (algebraMap (𝓞 K) K)*H x.1.val x.2.1 x.2.2).coeff l) := by
    have he := common_matrix_adjugate_entry φ C (B x.1) (H x.1.val)
      (hB x.1) x.2.1 x.2.2
    change IsIntegral ℤ ((φ C.det*H x.1.val x.2.1 x.2.2).coeff l)
    rw [he]
    change IsIntegral ℤ ((((B x.1*C.adjugate) x.2.1 x.2.2).map
      (algebraMap (𝓞 K) K)).coeff l)
    rw [Polynomial.coeff_map]
    exact NumberField.RingOfIntegers.isIntegral_coe _
  obtain ⟨hpos,hbound,hnorm,hint⟩ := polynomial_common_coefficient_natAbs_norm_certificate
    C.det k hk (fun x : Fin (s+1) × Fin r × Fin r => H x.1.val x.2.1 x.2.2) hprod
  have hshort : (r-1)*τ ≤ M := by
    calc
      (r-1)*τ ≤ (s+r-1)*τ := Nat.mul_le_mul_right τ (by omega)
      _ ≤ (s+r-1)*(τ+1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ M := hcut
  have hsize := typeIIIntegralLiftMatrix_coefficient_norm_bound r e N τ M T Q b
    hTe hQN HT HQ Hb hHT hHQ hHb hTH hQH hbH hshort k hk
  refine ⟨hpos,hsize.2, ?_⟩
  intro n hn i j l
  exact hint (⟨n,by omega⟩,i,j) l

end StrictEUnit
end
