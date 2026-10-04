import MatchgateWidth.MGIMatrixComposition
import MatchgateWidth.QuadraticInverse

/-! # Inverse closure in the exact ordered MGI matrix class

Every literal MGI is a linear functional of the tensor square. Since ordered
composition proves it on all nonnegative powers, finite-dimensional algebra
proves it on the inverse. No canonical-form or graphical closure is assumed.
-/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff Kronecker
variable {K : Type*} [Field K] {n : ℕ}

/-- The actual alternating MGI, linearized on matrix tensor squares. -/
def matrixMGIFunctional (α β : Finset (Fin (n + n))) :
    Matrix (BooleanInput n × BooleanInput n) (BooleanInput n × BooleanInput n) K →ₗ[K] K where
  toFun T :=
    let p := (α ∆ β).sort (· ≤ ·)
    ∑ j : Fin p.length, (-1 : K) ^ (j.val + 1) *
      T (((booleanSubsetEquiv n).symm (firstBlock (α ∆ {p[j]}))),
         ((booleanSubsetEquiv n).symm (firstBlock (β ∆ {p[j]}))))
        (((booleanSubsetEquiv n).symm (reversePortSubset (secondBlock (α ∆ {p[j]})))),
         ((booleanSubsetEquiv n).symm (reversePortSubset (secondBlock (β ∆ {p[j]})))))
  map_add' T U := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c T := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem matrixMGIFunctional_tensorSquare
    (α β : Finset (Fin (n + n))) (P : Matrix (BooleanInput n) (BooleanInput n) K) :
    matrixMGIFunctional α β (P ⊗ₖ P) =
      matchgateSum (orderedMatrixSubsetSignature P) α β ((α ∆ β).sort (· ≤ ·)) := by
  simp [matrixMGIFunctional, matchgateSum, orderedMatrixSubsetSignature,
    mul_assoc]

/-- A left inverse of a square ordered matchgate matrix is again an ordered
matchgate matrix. This includes zero wire width. -/
theorem OrderedMatchgateMatrix.leftInverse
    {P D : Matrix (BooleanInput n) (BooleanInput n) K}
    (hP : OrderedMatchgateMatrix P) (hDP : D * P = 1) :
    OrderedMatchgateMatrix D := by
  rw [orderedMatchgateMatrix_iff]
  intro α β
  have h := quadratic_equation_inverse_of_powers P D hDP
    (matrixMGIFunctional α β) (fun m => by
      rw [matrixMGIFunctional_tensorSquare]
      exact (orderedMatchgateMatrix_iff _).mp (hP.pow m) α β)
  simpa only [matrixMGIFunctional_tensorSquare] using h

/-- The usual nonsingular inverse is an ordered matchgate matrix. -/
theorem OrderedMatchgateMatrix.inv
    {P : Matrix (BooleanInput n) (BooleanInput n) K}
    (hP : OrderedMatchgateMatrix P) (hdet : IsUnit P.det) :
    OrderedMatchgateMatrix P⁻¹ :=
  hP.leftInverse (Matrix.nonsing_inv_mul P hdet)

end
end MatchgateWidth
