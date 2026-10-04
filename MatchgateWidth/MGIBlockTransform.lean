import MatchgateWidth.MGITensorPower

/-! # Exact all-block attachment of ordered matrices
The transformed tensor is the ordinary full finite sum/product, with every
old/new block in its original order and no scalar or hidden permutation.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K]

/-- Ordinary matrix action on the complete Boolean coordinate column. -/
def applyBooleanMatrix {r t : ℕ} (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (Q : BooleanTable t K) : BooleanTable r K := fun x => ∑ y, P x y * Q y

theorem OrderedMatchgateMatrix.applyBooleanMatrix {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K} (hP : OrderedMatchgateMatrix P)
    {Q : BooleanTable t K} (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (applyBooleanMatrix P Q) := by
  have h := hP.prefixTransform (s := 0) hQ
  have heq : MatchgateWidth.prefixTransform P (s := 0) Q = MatchgateWidth.applyBooleanMatrix P Q := by
    funext z
    simp only [MatchgateWidth.prefixTransform, MatchgateWidth.applyBooleanMatrix,
      Fin.castAdd_zero]
    apply Finset.sum_congr rfl
    intro x _
    congr 2
    funext i
    exact Fin.append_left x _ i
  rwa [heq] at h

/-- Replace each of k consecutive old blocks by the same ordered matrix. -/
def blockwiseTransform {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K) (k : ℕ)
    (Q : BooleanTable (k*t) K) : BooleanTable (k*r) K :=
  fun z => rightTransform P (fun x => Q (flattenBooleanBlocks x))
    ((booleanBlocksEquiv k r).symm z)

theorem blockwiseTransform_eq_tensorPower {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K) (k : ℕ)
    (Q : BooleanTable (k*t) K) :
    blockwiseTransform P k Q = applyBooleanMatrix (booleanTensorPower P k) Q := by
  classical
  funext z
  rw [applyBooleanMatrix, ← (booleanBlocksEquiv k t).sum_comp]
  simp only [blockwiseTransform, rightTransform, booleanTensorPower,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, tensorPowerMatrix]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  simp only [ booleanBlocksEquiv, Equiv.coe_fn_mk]
  ring

/-- Every actual blockwise tensor-power attachment preserves the literal MGI.
The conclusion includes k=0 and either wire width zero. -/
theorem OrderedMatchgateMatrix.blockwiseTransform {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K} (hP : OrderedMatchgateMatrix P)
    (k : ℕ) {Q : BooleanTable (k*t) K} (hQ : BooleanMatchgateIdentities Q) :
    BooleanMatchgateIdentities (MatchgateWidth.blockwiseTransform P k Q) := by
  rw [blockwiseTransform_eq_tensorPower]
  exact (hP.tensorPower k).applyBooleanMatrix hQ

end
end MatchgateWidth
