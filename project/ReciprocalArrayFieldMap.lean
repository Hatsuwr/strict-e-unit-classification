import SourceEulerMatrixFieldMap

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {K L : Type*} [Field K] [Field L]

theorem sameCompanionScalarTuple_field_map (phi : K →+* L) (r : ℕ) (hr : 0<r)
    (T : Polynomial K) (U : Matrix (Fin r) (Fin r) (Polynomial K)) (i : Fin (r+1)) :
    (sameCompanionScalarTuple r hr T U i).map phi=
      sameCompanionScalarTuple r hr (T.map phi) (fun i j =>(U i j).map phi) i := by
  cases i using Fin.lastCases <;> simp [sameCompanionScalarTuple]

theorem ordinaryReflectionTuple_field_map (phi : K →+* L) (m : ℕ)
    (q : Fin (m+1) →Polynomial K) (i : Fin (m+1)) :
    (ordinaryReflectionTuple m q i).map phi=
      ordinaryReflectionTuple m (fun i =>(q i).map phi) i := by
  apply Polynomial.ext
  intro j
  simp only [Polynomial.coeff_map,ordinaryReflectionTuple_coeff,map_mul,map_pow,map_neg,map_one]

theorem reciprocalGaugeCoefficient_field_map (phi : K →+* L) (i k : ℕ) :
    (reciprocalGaugeCoefficient (K:=K) i k).map phi=reciprocalGaugeCoefficient (K:=L) i k := by
  induction i generalizing k with
  | zero =>
    simp only [reciprocalGaugeCoefficient]
    split_ifs <;> simp
  | succ i ih =>
    simp only [reciprocalGaugeCoefficient,Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_neg,
      Polynomial.map_pow,Polynomial.map_X,← Polynomial.derivative_map,ih]
    split_ifs <;> simp [ih]

theorem reciprocalSourcePolynomial_field_map (phi : K →+* L) (m d k : ℕ)
    (q : Fin (m+1) →Polynomial K) :
    (reciprocalSourcePolynomial m d q k).map phi=
      reciprocalSourcePolynomial m d (fun i =>(q i).map phi) k := by
  simp only [reciprocalSourcePolynomial,Polynomial.map_sum,Polynomial.map_mul,
    ← Polynomial.reflect_map,reciprocalGaugeCoefficient_field_map]

theorem reciprocalCommonDegree_field_map (phi : K →+* L) (m : ℕ)
    (q : Fin (m+1) →Polynomial K) :
    reciprocalCommonDegree m (fun i =>(q i).map phi)=reciprocalCommonDegree m q := by
  simp only [reciprocalCommonDegree,Polynomial.natDegree_map_eq_of_injective phi.injective]

theorem reciprocalSourceDegree_field_map (phi : K →+* L) (m d : ℕ)
    (q : Fin (m+1) →Polynomial K) :
    reciprocalSourceDegree m d (fun i =>(q i).map phi)=reciprocalSourceDegree m d q := by
  simp only [reciprocalSourceDegree,← reciprocalSourcePolynomial_field_map,
    Polynomial.natDegree_map_eq_of_injective phi.injective]

/-- The literal reciprocal array transports without changing either order;
only the dependent Fin witness is cast along the proved degree equality. -/
theorem reciprocalSourceArray_field_map (phi : K →+* L) (m d : ℕ)
    (q : Fin (m+1) →Polynomial K) (k : Fin (m+1))
    (j : Fin (reciprocalSourceDegree m d (fun i =>(q i).map phi)+1)) :
    reciprocalSourceArray m d (fun i =>(q i).map phi) k j=
      phi (reciprocalSourceArray m d q k
        ⟨j.val,by rw [← reciprocalSourceDegree_field_map phi m d q]; exact j.isLt⟩) := by
  simp only [reciprocalSourceArray,← reciprocalSourcePolynomial_field_map,Polynomial.coeff_map]

end StrictEUnit
end
