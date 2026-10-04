import MatchgateWidth.GaussianOrderedMatrix

/-! # Exact Gaussian charts of arbitrary ordered MGI matrices -/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {r t : ℕ}

/-- The complete physical boundary word of a matrix coordinate. -/
def matrixBoundaryWord (x : BooleanInput r) (y : BooleanInput t) : BooleanInput (r + t) :=
  Fin.append x (fun j => y j.rev)

@[simp] theorem orderedMatrixSignature_boundaryWord
    (P : Matrix (BooleanInput r) (BooleanInput t) R) (x : BooleanInput r) (y : BooleanInput t) :
    orderedMatrixSignature P (matrixBoundaryWord x y) = P x y := by
  simp [orderedMatrixSignature, matrixBoundaryWord]

def boundaryInputBlock (M : Matrix (Fin (r+t)) (Fin (r+t)) R) : Matrix (Fin r) (Fin r) R :=
  M.submatrix (Fin.castAdd t) (Fin.castAdd t)
def boundaryCrossBlock (M : Matrix (Fin (r+t)) (Fin (r+t)) R) : Matrix (Fin r) (Fin t) R :=
  M.submatrix (Fin.castAdd t) (fun j => Fin.natAdd r j.rev)
def boundaryOutputBlock (M : Matrix (Fin (r+t)) (Fin (r+t)) R) : Matrix (Fin t) (Fin t) R :=
  M.submatrix (fun j => Fin.natAdd r j.rev) (fun j => Fin.natAdd r j.rev)

theorem gaussian_boundary_blocks (M : Matrix (Fin (r+t)) (Fin (r+t)) R)
    (hM : ∀ i j, M i j = -M j i) :
    (gaussianFullMatrix (boundaryInputBlock M) (boundaryCrossBlock M)
      (boundaryOutputBlock M)).submatrix gaussianBoundaryMode gaussianBoundaryMode = M := by
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [gaussianBoundaryMode, gaussianFullMatrix, boundaryInputBlock,
      boundaryCrossBlock, boundaryOutputBlock]
  exact (hM _ _).symm

theorem gaussian_boundary_value (M : Matrix (Fin (r+t)) (Fin (r+t)) R)
    (hM : ∀ i j, M i j = -M j i) (x : BooleanInput r) (y : BooleanInput t) :
    gaussianOrderedMatrix (boundaryInputBlock M) (boundaryCrossBlock M)
      (boundaryOutputBlock M) x y =
      principalPfaffian M (booleanSubsetEquiv (r+t) (matrixBoundaryWord x y)) := by
  have h := gaussianOrderedMatrix_subset (boundaryInputBlock M) (boundaryCrossBlock M)
    (boundaryOutputBlock M) (booleanSubsetEquiv (r+t) (matrixBoundaryWord x y))
  rw [gaussian_boundary_blocks M hM, ← orderedMatrixSignature_subset,
    Equiv.symm_apply_apply, orderedMatrixSignature_boundaryWord] at h
  exact h

theorem matrixBoundaryWord_xor (p z : BooleanInput (r+t)) :
    pfaffianXor p z = matrixBoundaryWord
      (pfaffianXor (fun i => p (Fin.castAdd t i)) (fun i => z (Fin.castAdd t i)))
      (pfaffianXor (fun j => p (Fin.natAdd r j.rev)) (fun j => z (Fin.natAdd r j.rev))) := by
  funext i
  induction i using Fin.addCases <;> simp [matrixBoundaryWord, pfaffianXor]

section Field
variable {K : Type*} [Field K]
/-- Every ordered MGI matrix has a literal scaled Gaussian chart after separate
input and output XORs. All block matrices are constructed from its chart. -/
theorem OrderedMatchgateMatrix.exists_gaussian_chart
    {P : Matrix (BooleanInput r) (BooleanInput t) K} (hP : OrderedMatchgateMatrix P) :
    ∃ (p : BooleanInput r) (q : BooleanInput t) (c : K)
      (A : Matrix (Fin r) (Fin r) K) (B : Matrix (Fin r) (Fin t) K)
      (D : Matrix (Fin t) (Fin t) K),
      (∀ i j, A i j = -A j i) ∧ (∀ i j, D i j = -D j i) ∧
      (∀ i, A i i = 0) ∧ (∀ i, D i i = 0) ∧
      ∀ x y, P x y = c * gaussianOrderedMatrix A B D (pfaffianXor p x) (pfaffianXor q y) := by
  obtain ⟨pivot, a, ha⟩ := hP.exists_pfaffianPivotChart
  let M := pfaffianChartMatrix a
  have hM : ∀ i j, M i j = -M j i := fun i j => pfaffianChartMatrix_skew a j i
  refine ⟨(fun i => pivot (Fin.castAdd t i)), (fun j => pivot (Fin.natAdd r j.rev)),
    a none, boundaryInputBlock M, boundaryCrossBlock M, boundaryOutputBlock M,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; exact hM _ _
  · intro i j; exact hM _ _
  · intro i; exact pfaffianChartMatrix_diag a _
  · intro i; exact pfaffianChartMatrix_diag a _
  · intro x y
    have h := congrFun ha (matrixBoundaryWord x y)
    rw [orderedMatrixSignature_boundaryWord] at h
    rw [gaussian_boundary_value M hM]
    rw [h]
    simp only [pfaffianPivotChart,  Fin.val_zero, pow_zero, one_mul, pfaffianChart]
    congr 1
    change pfaffianList M _ = pfaffianList M _
    congr 1
    change (booleanSubsetEquiv (r+t) (pfaffianXor pivot (matrixBoundaryWord x y))).sort _ = _
    rw [matrixBoundaryWord_xor]
    simp [matrixBoundaryWord]
end Field
end
end MatchgateWidth
