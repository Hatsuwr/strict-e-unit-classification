import OrderedMomentGaugeDerivative

noncomputable section
open scoped BigOperators Classical Matrix
namespace StrictEUnit
variable {K : Type*} [Field K] [CharZero K]

theorem linearEquiv_matrix_twoSided {R : Type*} [CommRing R] {r : ℕ}
    (e : (Fin r →R) ≃ₗ[R] (Fin r →R)) :
    LinearMap.toMatrix' e.toLinearMap*LinearMap.toMatrix' e.symm.toLinearMap=1 ∧
    LinearMap.toMatrix' e.symm.toLinearMap*LinearMap.toMatrix' e.toLinearMap=1 := by
  rw [← LinearMap.toMatrix'_comp,← LinearMap.toMatrix'_comp]
  have ha : e.toLinearMap.comp e.symm.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact e.apply_symm_apply v
  have hb : e.symm.toLinearMap.comp e.toLinearMap=LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact e.symm_apply_apply v
  simp only [ha,hb,LinearMap.toMatrix'_id,and_self]

theorem actualOrderedMoment_matrix_connection {r s : ℕ}
    (C : Matrix (Fin r) (Fin r) (PowerSeries K)) (g : Fin r →PowerSeries K)
    (M : ℕ) (k : ℕ →ℤ) (lam a : Fin (s+1) →K)
    (hlam : ∀ j,lam j=(((M:ℤ)+k j.val):K))
    (ha : ∀ j,lam j^(s+1)=∑ m : Fin (s+1),a m*lam j^m.val)
    (hV : IsUnit (((forcingMomentMatrix lam).map (PowerSeries.C K)).det)) :
    let e := orderedSystemGauge r (s+1) ((forcingMomentMatrix lam).map (PowerSeries.C K)) hV
    let G := LinearMap.toMatrix' e.toLinearMap
    Matrix.of (fun i j =>powerSeriesEuler (G i j))+G*finiteLaurentEulerMatrix C g M k (s+1)=
      orderedMomentConnection C g (fun j =>PowerSeries.C K (a j))*G := by
  intro e G
  rw [orderedSystemGauge_matrix_derivative_zero,zero_add]
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  change (G*finiteLaurentEulerMatrix C g M k (s+1)).mulVec v=
    (orderedMomentConnection C g (fun j =>PowerSeries.C K (a j))*G).mulVec v
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec]
  have hg (w : Fin (r+(s+1)) →PowerSeries K) : G.mulVec w=e w := by
    change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) w=e w
    rw [Matrix.toLin'_toMatrix']
    rfl
  rw [hg,hg]
  exact actualOrderedMoment_intertwines C g M k lam a hlam ha hV v

/-- A constructed frame for the ACTUAL finite Laurent source extension.
Only splitting of its constructed scalar indicial polynomial remains exposed;
no frame, determinant, cyclic shape, or gauge identity is assumed. -/
theorem actualFiniteLaurentSource_constructed_frame
    (n s M L : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0)
    (k : ℕ →ℤ)
    (hinj : Function.Injective (fun j : Fin (s+1) =>(((L:ℤ)+k j.val):K))) :
    let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) L k (s+1)
    ∃ b : Fin (((n+1)+(s+1))+1) →PowerSeries K,
      b (Fin.last ((n+1)+(s+1)))=1 ∧
      ∀ hsplit : (scalarEulerCoefficientSymbol ((n+1)+(s+1))
        (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K),
      ∃ rho : Fin ((n+1)+(s+1)) →K,
      ∃ Y : Matrix (Fin ((n+1)+(s+1))) (Fin ((n+1)+(s+1))) (Polynomial (LaurentSeries K)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  intro C
  let lam : Fin (s+1) →K := fun j =>(((L:ℤ)+k j.val):K)
  obtain ⟨a,ha⟩ := forcingMoment_closure_coefficients lam hinj
  have hV : IsUnit (((forcingMomentMatrix lam).map (PowerSeries.C K)).det) := by
    change IsUnit (((PowerSeries.C K).mapMatrix (forcingMomentMatrix lam)).det)
    rw [← RingHom.map_det]
    exact (isUnit_iff_ne_zero.mpr (forcingMomentMatrix_det_ne_zero lam hinj)).map (PowerSeries.C K)
  let e := orderedSystemGauge (n+1) (s+1) ((forcingMomentMatrix lam).map (PowerSeries.C K)) hV
  let G := LinearMap.toMatrix' e.toLinearMap
  let H := LinearMap.toMatrix' e.symm.toLinearMap
  obtain ⟨hg,hh⟩ := linearEquiv_matrix_twoSided e
  have hc := actualOrderedMoment_matrix_connection (sourceLaurentEulerBase n T U M)
    (augmentedSourceEulerColumn n T) L k lam a (fun j =>rfl) ha hV
  obtain ⟨b,hb,hframe⟩ := orderedSourceMoment_constructed_frame n s M T U hT (fun j =>PowerSeries.C K (a j))
  refine ⟨b,hb,fun hsplit =>?_⟩
  obtain ⟨rho,Z,hdet,hZ⟩ := hframe hsplit
  exact ⟨rho,H.map logPowerSeriesEmbedding*Z,
    regularEuler_log_frame_pullback C _ G H hg hh hc rho Z hZ hdet⟩

/-- Exact forcing pattern and common offset of the actual zero-class preimage.
Distinctness is proved from the integer residual indices, not assumed. -/
theorem actualResidualSource_constructed_frame (n d s : ℕ) (T : Polynomial K)
    (U : Matrix (Fin (n+1)) (Fin (n+1)) (Polynomial K)) (hT : T≠0) :
    let k := fun j : ℕ =>(d:ℤ)-(j:ℤ)
    let M := finiteLaurentOffset k (s+1)
    let C := finiteLaurentEulerMatrix (sourceLaurentEulerBase n T U M)
      (augmentedSourceEulerColumn n T) (M+(n+1)) k (s+1)
    ∃ b : Fin (((n+1)+(s+1))+1) →PowerSeries K,
      b (Fin.last ((n+1)+(s+1)))=1 ∧
      ∀ hsplit : (scalarEulerCoefficientSymbol ((n+1)+(s+1))
        (fun i k =>PowerSeries.coeff K k (b i)) 0).Splits (RingHom.id K),
      ∃ rho : Fin ((n+1)+(s+1)) →K,
      ∃ Y : Matrix (Fin ((n+1)+(s+1))) (Fin ((n+1)+(s+1))) (Polynomial (LaurentSeries K)),
        Y.det≠0 ∧ (∀ j i,twistedLogPolynomialEuler (rho j) (Y i j)=
          ∑ l,logPowerSeriesEmbedding (C i l)*Y l j) := by
  intro k M C
  apply actualFiniteLaurentSource_constructed_frame n s M (M+(n+1)) T U hT k
  have hi := shiftedResidualEigenvalues_injective (K:=K) (s+1) ((M+(n+1):ℕ):ℤ) (d:ℤ)
  convert hi using 1
  funext j
  dsimp [k]
  push_cast
  ring

end StrictEUnit
end
