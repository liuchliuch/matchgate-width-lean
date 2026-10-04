import MatchgateWidth.IsotropicKernelCover

/-! # Matrix representation of actual coefficient-spinor operators
Target coordinates index rows and source coordinates index columns. The
transpose therefore has row space equal to the operator range.
-/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {t : ℕ}

/-- Actual Boolean-coordinate matrix of an operator on subset spinors. -/
def spinorOperatorMatrix (f : Module.End R (SubsetSignature t R)) :
    Matrix (BooleanInput t) (BooleanInput t) R :=
  (LinearMap.toMatrix' f).submatrix (booleanSubsetEquiv t) (booleanSubsetEquiv t)

@[simp] theorem spinorOperatorMatrix_apply (f : Module.End R (SubsetSignature t R))
    (x y : BooleanInput t) :
    spinorOperatorMatrix f x y = f (Pi.single (booleanSubsetEquiv t y) 1) (booleanSubsetEquiv t x) := rfl

@[simp] theorem spinorOperatorMatrix_one :
    spinorOperatorMatrix (1 : Module.End R (SubsetSignature t R)) = 1 := by
  rw [spinorOperatorMatrix, LinearMap.toMatrix'_one, Matrix.submatrix_one_equiv]

@[simp] theorem spinorOperatorMatrix_mul (f g : Module.End R (SubsetSignature t R)) :
    spinorOperatorMatrix (f * g) = spinorOperatorMatrix f * spinorOperatorMatrix g := by
  simp only [spinorOperatorMatrix, LinearMap.toMatrix'_mul, Matrix.submatrix_mul_equiv]

/-- The source vector is first decoded to subset coefficients, the genuine
operator acts, and the result is reencoded to Boolean coefficients. -/
theorem spinorOperatorMatrix_mulVec (f : Module.End R (SubsetSignature t R))
    (u : BooleanTable t R) :
    Matrix.mulVec (spinorOperatorMatrix f) u = spinorSubsetEquiv.symm (f (spinorSubsetEquiv u)) := by
  ext x
  change (∑ y, f (Pi.single (booleanSubsetEquiv t y) 1) (booleanSubsetEquiv t x) * u y) = _
  have hdecomp : spinorSubsetEquiv u = ∑ y, u y • Pi.single (booleanSubsetEquiv t y) 1 := by
    ext S
    simp only [spinorSubsetEquiv_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero]
    simp_rw [← (booleanSubsetEquiv t).symm_apply_eq]
    simp
  rw [hdecomp, map_sum]
  simp [Finset.sum_apply, map_smul, spinorSubsetEquiv, LinearEquiv.funCongrLeft, mul_comm]

/-- Exact range/row-space correspondence, with the coordinate equivalence visible. -/
theorem spinorOperatorMatrix_transpose_rowSpace (f : Module.End R (SubsetSignature t R)) :
    (orderedRowSpace (spinorOperatorMatrix f).transpose).map spinorSubsetEquiv.toLinearMap =
      LinearMap.range f := by
  ext v
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [orderedRowSpace, Matrix.row_transpose, ← Matrix.range_mulVecLin] at hu
    obtain ⟨w, rfl⟩ := hu
    refine ⟨spinorSubsetEquiv w, ?_⟩
    change _ = spinorSubsetEquiv (Matrix.mulVec (spinorOperatorMatrix f) w)
    rw [spinorOperatorMatrix_mulVec, spinorSubsetEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    refine ⟨spinorSubsetEquiv.symm (f u), ?_, spinorSubsetEquiv.apply_symm_apply _⟩
    rw [orderedRowSpace, Matrix.row_transpose, ← Matrix.range_mulVecLin]
    refine ⟨spinorSubsetEquiv.symm u, ?_⟩
    change Matrix.mulVec (spinorOperatorMatrix f) (spinorSubsetEquiv.symm u) = _
    rw [spinorOperatorMatrix_mulVec, spinorSubsetEquiv.apply_symm_apply]

variable {K : Type*} [Field K]

/-- Matrix rank is the genuine operator image dimension. -/
theorem spinorOperatorMatrix_rank (f : Module.End K (SubsetSignature t K)) :
    (spinorOperatorMatrix f).rank = Module.finrank K (LinearMap.range f) := by
  rw [← spinorOperatorMatrix_transpose_rowSpace]
  rw [← (spinorSubsetEquiv.submoduleMap (orderedRowSpace (spinorOperatorMatrix f).transpose)).finrank_eq]
  rw [orderedRowSpace, ← Matrix.rank_eq_finrank_span_row, Matrix.rank_transpose]

end
end MatchgateWidth
