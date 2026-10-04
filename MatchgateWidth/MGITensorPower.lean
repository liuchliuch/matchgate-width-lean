import MatchgateWidth.MGIMatrixParallel
import MatchgateWidth.TransformedSupport

/-! # Genuine tensor powers of ordered matchgate matrices -/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K]

/-- Transport input/output arities through equalities without permuting wires. -/
def castOrderedMatrix {r t r' t' : ℕ} (hr : r = r') (ht : t = t')
    (P : Matrix (BooleanInput r) (BooleanInput t) K) :
    Matrix (BooleanInput r') (BooleanInput t') K :=
  fun x y => P (x ∘ Fin.cast hr) (y ∘ Fin.cast ht)

theorem OrderedMatchgateMatrix.castInputsOutputs {r t r' t' : ℕ}
    (hr : r = r') (ht : t = t') {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) : OrderedMatchgateMatrix (castOrderedMatrix hr ht P) := by
  cases hr
  cases ht
  exact hP

/-- The ordinary tensor power, reindexed by the certified block-major word
bijection on both sides. -/
def booleanTensorPower {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K) (k : ℕ) :
    Matrix (BooleanInput (k*r)) (BooleanInput (k*t)) K :=
  (tensorPowerMatrix (P := Fin k) P).submatrix
    (booleanBlocksEquiv k r).symm (booleanBlocksEquiv k t).symm

@[simp] theorem booleanTensorPower_zero {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K) :
    booleanTensorPower P 0 = castOrderedMatrix (Nat.zero_mul r).symm (Nat.zero_mul t).symm
      (1 : Matrix (BooleanInput 0) (BooleanInput 0) K) := by
  ext x y
  simp [booleanTensorPower, tensorPowerMatrix, castOrderedMatrix, Matrix.one_apply,
    Subsingleton.elim (x ∘ Fin.cast (Nat.zero_mul r).symm) (y ∘ Fin.cast (Nat.zero_mul t).symm)]

theorem booleanTensorPower_succ {r t : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K) (k : ℕ) :
    booleanTensorPower P (k+1) = castOrderedMatrix
      (show r+k*r = (k+1)*r by ring) (show t+k*t = (k+1)*t by ring)
      (orderedMatrixParallel P (booleanTensorPower P k)) := by
  ext x y
  simp only [booleanTensorPower, tensorPowerMatrix, Matrix.submatrix_apply,
    booleanBlocksEquiv, Equiv.coe_fn_symm_mk, Fin.prod_univ_succ,
    castOrderedMatrix, orderedMatrixParallel, Function.comp_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg₂ P
  · funext j
    apply congrArg x
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  · funext j
    apply congrArg y
    apply Fin.ext
    simp [finProdFinEquiv]
    ring

/-- Every ordinary tensor power is an ordered matchgate matrix. This proves
blockwise attachment closure without assuming an arbitrary block permutation. -/
theorem OrderedMatchgateMatrix.tensorPower {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (k : ℕ) :
    OrderedMatchgateMatrix (booleanTensorPower P k) := by
  induction k with
  | zero =>
    rw [booleanTensorPower_zero]
    exact (OrderedMatchgateMatrix.one (R := K) 0).castInputsOutputs _ _
  | succ k ih =>
    rw [booleanTensorPower_succ]
    exact (hP.parallel ih).castInputsOutputs _ _

end
end MatchgateWidth
