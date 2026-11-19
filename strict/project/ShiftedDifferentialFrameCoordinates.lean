import DifferentialFrameCoordinates

noncomputable section
open scoped BigOperators
namespace StrictEUnit
variable {R : Type*} [CommRing R]

theorem shiftedDifferentialFrame_coordinates {r : ℕ} (D : R →+ R)
    (hD : ∀ x y,D (x*y)=D x*y+x*D y)
    (C H J : Matrix (Fin r) (Fin r) R) (rho : Fin r → R) (xi : R)
    (hJ : J*H=1) (hH : H*J=1)
    (hdH : (fun i j =>D (H i j))=C*H-H*Matrix.diagonal rho)
    (u : Fin r → R) (hu : ∀ i,D (u i)=(C.mulVec u) i-xi*u i) :
    let v := J.mulVec u
    H.mulVec v=u ∧ ∀ j,D (v j)=(rho j-xi)*v j := by
  have hframe : (fun i j =>D (H i j))=
      (C-Matrix.diagonal (fun _ : Fin r =>xi))*H-H*Matrix.diagonal (fun j =>rho j-xi) := by
    rw [hdH,Matrix.sub_mul]
    ext i j
    change (C*H) i j-(H*Matrix.diagonal rho) i j=
      ((C*H) i j-((Matrix.diagonal (fun _ : Fin r =>xi))*H) i j)-(H*Matrix.diagonal (fun j =>rho j-xi)) i j
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.mul_diagonal]
    ring
  have hsolution : (fun i =>D (u i))=(C-Matrix.diagonal (fun _ : Fin r =>xi)).mulVec u := by
    ext i
    rw [hu,Matrix.sub_mulVec]
    simp only [Pi.sub_apply,Matrix.mulVec_diagonal]
  obtain ⟨hv,hd⟩ := differentialFrame_coordinates D hD _ _ H J hJ hH hframe u hsolution
  refine ⟨hv,?_⟩
  intro j
  have h := congrFun hd j
  simpa only [Matrix.mulVec_diagonal] using h

end StrictEUnit
end
