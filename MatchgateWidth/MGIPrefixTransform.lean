import MatchgateWidth.GaussianMatrixCharts

/-! # Ordered substitution at a consecutive boundary prefix

The prefix matrix's outputs meet the old tensor's prefix in opposite physical
order. The resulting literal signature retains the new prefix and the old
suffix without an undocumented permutation or scalar.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {r t s : ℕ}

/-- View a Boolean tensor as an ordered matrix across a consecutive cut. -/
def prefixTensorMatrix (Q : BooleanTable (t+s) R) :
    Matrix (BooleanInput t) (BooleanInput s) R :=
  fun x z => Q (matrixBoundaryWord x z)

@[simp] theorem orderedMatrixSignature_prefixTensorMatrix (Q : BooleanTable (t+s) R) :
    orderedMatrixSignature (prefixTensorMatrix Q) = Q := by
  funext z
  unfold orderedMatrixSignature prefixTensorMatrix
  congr 1
  funext i
  induction i using Fin.addCases <;> simp [matrixBoundaryWord]

theorem prefixTensorMatrix_isMatchgate {Q : BooleanTable (t+s) R}
    (hQ : BooleanMatchgateIdentities Q) : OrderedMatchgateMatrix (prefixTensorMatrix Q) := by
  unfold OrderedMatchgateMatrix
  rwa [orderedMatrixSignature_prefixTensorMatrix]

/-- Actual finite contraction replacing a first consecutive block. -/
def prefixTransform (P : Matrix (BooleanInput r) (BooleanInput t) R)
    (Q : BooleanTable (t+s) R) : BooleanTable (r+s) R :=
  fun z => ∑ x : BooleanInput t,
    P (fun i => z (Fin.castAdd s i)) x * Q (Fin.append x (fun j => z (Fin.natAdd r j)))

/-- No coordinate convention is hidden in the matrix composition. -/
theorem prefixTransform_eq_orderedSignature
    (P : Matrix (BooleanInput r) (BooleanInput t) R) (Q : BooleanTable (t+s) R) :
    prefixTransform P Q = orderedMatrixSignature (P * prefixTensorMatrix Q) := by
  funext z
  simp [prefixTransform, orderedMatrixSignature, Matrix.mul_apply,
    prefixTensorMatrix, matrixBoundaryWord]

/-- Ordered MGI matrices may be attached to a consecutive tensor prefix. -/
theorem OrderedMatchgateMatrix.prefixTransform
    {P : Matrix (BooleanInput r) (BooleanInput t) R} (hP : OrderedMatchgateMatrix P)
    {Q : BooleanTable (t+s) R} (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (prefixTransform P Q) := by
  rw [prefixTransform_eq_orderedSignature]
  exact hP.mul (prefixTensorMatrix_isMatchgate hQ)

end
end MatchgateWidth
