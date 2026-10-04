import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Linear support under residual contraction

This module proves the matrix algebra used in Lemmas 10.1 and 10.2 of
arXiv:2610.00079v1. The application to actual planar gadget boundary tensors
still requires the network contraction-to-matrix-product bridge; this module
does not assert that the complete gadget lemmas have been formalized.
-/

namespace MatchgateWidth

noncomputable section

variable {K I J L O : Type*} [Field K]
variable [Fintype I] [Fintype J] [Fintype L] [Fintype O]

/-- Column support, using ordinary bilinear coordinates, never conjugation. -/
def columnSupport (A : Matrix I J K) : Submodule K (I → K) :=
  LinearMap.range A.mulVecLin

/-- Contracting the complementary indices cannot enlarge the boundary support. -/
theorem columnSupport_mul_le (A : Matrix I J K) (B : Matrix J L K) :
    columnSupport (A * B) ≤ columnSupport A := by
  intro x hx
  rcases hx with ⟨v, hv⟩
  refine ⟨B.mulVecLin v, ?_⟩
  rw [Matrix.mulVecLin_mul] at hv
  exact hv

/-- Surjective changes of complementary coordinates preserve the support. -/
theorem columnSupport_mul_eq (A : Matrix I J K) (B : Matrix J L K)
    (hB : Function.Surjective B.mulVecLin) :
    columnSupport (A * B) = columnSupport A := by
  apply le_antisymm (columnSupport_mul_le A B)
  intro x hx
  rcases hx with ⟨v, hv⟩
  rcases hB v with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  rw [Matrix.mulVecLin_mul]
  change A.mulVecLin (B.mulVecLin w) = x
  rw [hw, hv]

/-- A change of coordinates on the exposed port maps its support exactly. -/
theorem columnSupport_left_mul (A : Matrix I J K) (C : Matrix O I K) :
    columnSupport (C * A) = (columnSupport A).map C.mulVecLin := by
  ext x
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨A.mulVecLin v, ⟨v, rfl⟩, by
      rw [Matrix.mulVecLin_mul] at hv
      exact hv⟩
  · rintro ⟨y, ⟨v, hv⟩, hy⟩
    refine ⟨v, ?_⟩
    rw [Matrix.mulVecLin_mul]
    change C.mulVecLin (A.mulVecLin v) = x
    rw [hv, hy]

/-- Combined coordinate change, in the precise flattening matrix form. -/
theorem columnSupport_transformed (A : Matrix I J K) (B : Matrix J L K)
    (C : Matrix O I K) (hB : Function.Surjective B.mulVecLin) :
    columnSupport (C * A * B) = (columnSupport A).map C.mulVecLin := by
  rw [columnSupport_mul_eq (C * A) B hB, columnSupport_left_mul]

end
end MatchgateWidth
