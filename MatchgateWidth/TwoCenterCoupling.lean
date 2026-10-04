import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic

/-!
# Exact two-center tensor contraction

The coordinate computation and rank argument of Proposition 8.3. The tensor
`controlledLinks` is the coordinate form from Proposition 8.1; equality with
the paper's Pfaffian-realized right signature is a separate open bridge.
The finite contraction below includes both binary disequality vertices.
-/

namespace MatchgateWidth

noncomputable section

variable {K X : Type*} [Field K] [Fintype X]

/-- Binary qutrit disequality supported on states zero and one. -/
def neq01 (a b : Fin 3) : K :=
  if (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) then 1 else 0

/-- The two link coordinates of the controlled right tensor. -/
def controlledLinks (f w : X → K) (a b : Fin 3) (x : X) : K :=
  if a = 0 ∧ b = 0 then f x else if a = 1 ∧ b = 1 then w x * f x else 0

/-- Actual four internal edge sums, retaining the cross-paired link names. -/
def coupledBoundary (f w : X → K) (x y : X) : K :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    controlledLinks f w a b x * controlledLinks f w c d y *
      neq01 b c * neq01 a d

/-- Exactly the two unequal common link states survive. -/
theorem coupledBoundary_eq (f w : X → K) (x y : X) :
    coupledBoundary f w x y = f x * f y * (w x + w y) := by
  simp [coupledBoundary, controlledLinks, neq01, Fin.sum_univ_succ]
  ring

def couplingLeftFactor (f w : X → K) : Matrix X (Fin 2) K :=
  fun x i => if i = 0 then f x * w x else f x

def couplingRightFactor (f w : X → K) : Matrix (Fin 2) X K :=
  fun i y => if i = 0 then f y else f y * w y

/-- The full boundary matrix is a sum of two outer products. -/
theorem coupledBoundary_factor (f w : X → K) :
    (coupledBoundary f w : Matrix X X K) =
      couplingLeftFactor f w * couplingRightFactor f w := by
  ext x y
  rw [coupledBoundary_eq, Matrix.mul_apply]
  simp [couplingLeftFactor, couplingRightFactor, Fin.sum_univ_succ]
  ring

/-- The contraction therefore has Schmidt rank at most two. -/
theorem coupledBoundary_rank_le_two (f w : X → K) :
    Matrix.rank (coupledBoundary f w : Matrix X X K) ≤ 2 := by
  rw [coupledBoundary_factor]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa using (Matrix.rank_le_card_width (couplingLeftFactor f w)))

/-- The displayed two-by-two minor is nonzero when both control values occur. -/
theorem coupledBoundary_minor_det (f w : X → K) (x y : X) :
    Matrix.det (Matrix.submatrix (coupledBoundary f w : Matrix X X K) ![x,y] ![x,y]) =
      -(f x * f y * (w x - w y)) ^ 2 := by
  simp [Matrix.det_fin_two, Matrix.submatrix, coupledBoundary_eq]
  ring

/-- Exact rank two, including all additional zero rows outside the hard support. -/
theorem coupledBoundary_rank_eq_two (f w : X → K) (x y : X)
    (hx : f x ≠ 0) (hy : f y ≠ 0) (hw : w x ≠ w y) :
    Matrix.rank (coupledBoundary f w : Matrix X X K) = 2 := by
  have hd : Matrix.det (Matrix.submatrix (coupledBoundary f w : Matrix X X K) ![x,y] ![x,y]) ≠ 0 := by
    rw [coupledBoundary_minor_det]
    exact neg_ne_zero.mpr (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hx hy) (sub_ne_zero.mpr hw)))
  have hl := Matrix.rank_submatrix_le (coupledBoundary f w : Matrix X X K) ![x,y] ![x,y]
  rw [Matrix.rank_of_det_ne_zero hd, Fintype.card_fin] at hl
  exact le_antisymm (coupledBoundary_rank_le_two f w) hl

end
end MatchgateWidth
