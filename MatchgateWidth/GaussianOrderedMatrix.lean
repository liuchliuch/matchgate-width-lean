import MatchgateWidth.GaussianFullRank
import MatchgateWidth.MGIMatrixInverse
import MatchgateWidth.PfaffianIdentities
import MatchgateWidth.BaseDecoder

/-! # Gaussian coefficients in the literal ordered matrix convention -/
namespace MatchgateWidth
noncomputable section
variable {R : Type*} [CommRing R] {r t : ℕ}

/-- Boolean coordinates of the actual Gaussian matrix, with increasing input
modes and decreasing output modes in its Pfaffian boundary order. -/
def gaussianOrderedMatrix (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r) (Fin t) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix (BooleanInput r) (BooleanInput t) R :=
  (gaussianFullPlanarPfaffianMatrix A B D).submatrix
    (booleanSubsetEquiv r) (booleanSubsetEquiv t)

/-- Physical boundary position to Gaussian mode, including output reversal. -/
def gaussianBoundaryMode : Fin (r + t) → Fin r ⊕ Fin t :=
  Fin.addCases Sum.inl (fun j => Sum.inr j.rev)

@[simp] theorem gaussianBoundaryMode_input (i : Fin r) :
    gaussianBoundaryMode (Fin.castAdd t i) = Sum.inl i := by
  simp [gaussianBoundaryMode]
@[simp] theorem gaussianBoundaryMode_output (j : Fin t) :
    gaussianBoundaryMode (Fin.natAdd r j) = Sum.inr j.rev := by
  simp [gaussianBoundaryMode]

/-- The literal ordered signature is precisely a principal-Pfaffian chart of
the physically enumerated skew matrix. -/
theorem gaussianOrderedMatrix_subset (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r) (Fin t) R) (D : Matrix (Fin t) (Fin t) R)
    (S : Finset (Fin (r + t))) :
    orderedMatrixSubsetSignature (gaussianOrderedMatrix A B D) S =
      principalPfaffian ((gaussianFullMatrix A B D).submatrix
        gaussianBoundaryMode gaussianBoundaryMode) S := by
  simp only [orderedMatrixSubsetSignature, gaussianOrderedMatrix, Matrix.submatrix_apply,
    Equiv.apply_symm_apply, gaussianFullPlanarPfaffianMatrix, gaussianFullPfaffian,
    gaussianSubsetList_eq_sort, sort_reversePortSubset, List.reverse_reverse]
  change _ = pfaffianList (fun i j => gaussianFullMatrix A B D
    (gaussianBoundaryMode i) (gaussianBoundaryMode j)) (S.sort (· ≤ ·))
  conv_rhs => rw [← pfaffianList_map (gaussianFullMatrix A B D) gaussianBoundaryMode]
  rw [sort_blocks]
  simp only [List.map_append, List.map_map, Function.comp_def,
    gaussianBoundaryMode_input, gaussianBoundaryMode_output]

theorem gaussianOrderedMatrix_isMatchgate (A : Matrix (Fin r) (Fin r) R)
    (B : Matrix (Fin r) (Fin t) R) (D : Matrix (Fin t) (Fin t) R)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i)
    (hA0 : ∀ i, A i i = 0) (hD0 : ∀ i, D i i = 0) :
    OrderedMatchgateMatrix (gaussianOrderedMatrix A B D) := by
  rw [orderedMatchgateMatrix_iff]
  have heq : orderedMatrixSubsetSignature (gaussianOrderedMatrix A B D) =
      principalPfaffian ((gaussianFullMatrix A B D).submatrix
        gaussianBoundaryMode gaussianBoundaryMode) := by
    funext S
    exact gaussianOrderedMatrix_subset A B D S
  rw [heq]
  apply principalPfaffian_matchgateIdentities
  · intro i j
    exact gaussianFullMatrix_skew A B D hA hD _ _
  · intro i
    change gaussianFullMatrix A B D (gaussianBoundaryMode i) (gaussianBoundaryMode i) = 0
    cases gaussianBoundaryMode i with
    | inl j => exact hA0 j
    | inr j => exact hD0 j

section Field
variable {K : Type*} [Field K] [CharZero K]

theorem gaussianOrderedMatrix_rank (A : Matrix (Fin r) (Fin r) K)
    (B : Matrix (Fin r) (Fin t) K) (D : Matrix (Fin t) (Fin t) K)
    (hA : ∀ i j, A i j = -A j i) (hD : ∀ i j, D i j = -D j i) :
    (gaussianOrderedMatrix A B D).rank = 2 ^ B.rank := by
  unfold gaussianOrderedMatrix
  rw [Matrix.rank_submatrix]
  exact gaussianFullPlanarPfaffianMatrix_rank A B D hA hD

/-- A square Gaussian with identity cross block has full rank even with an
arbitrary skew output block. -/
theorem gaussianOrderedMatrix_identity_cross_rank (D : Matrix (Fin t) (Fin t) K)
    (hD : ∀ i j, D i j = -D j i) :
    (gaussianOrderedMatrix 0 (1 : Matrix (Fin t) (Fin t) K) D).rank =
      Fintype.card (BooleanInput t) := by
  rw [gaussianOrderedMatrix_rank _ _ _ (by simp) hD, Matrix.rank_one]
  simp [BooleanInput]

/-- Negating the output quadratic block compensates exactly for physical
output reversal, so the vacuum row is the increasing principal-Pfaffian table. -/
theorem gaussianOrderedMatrix_vacuum_row (D : Matrix (Fin t) (Fin t) K)
    (hD : ∀ i j, D i j = -D j i) (z : BooleanInput t) :
    gaussianOrderedMatrix 0 (1 : Matrix (Fin t) (Fin t) K) (-D) (fun _ => 0) z =
      principalPfaffian D (booleanSubsetEquiv t z) := by
  simp only [gaussianOrderedMatrix, Matrix.submatrix_apply, booleanSubsetEquiv_zero,
    gaussianFullPlanarPfaffianMatrix, gaussianSubsetList_eq_sort, Finset.sort_empty,
    gaussianFullPfaffian_nil]
  exact pfaffianList_neg_reverse D hD _

/-- Every normalized principal-Pfaffian row occurs as the vacuum row of an
invertible ordered matchgate matrix, with an ordered matchgate inverse. -/
theorem exists_invertible_gaussian_with_vacuum_row
    (D : Matrix (Fin t) (Fin t) K) (hD : ∀ i j, D i j = -D j i)
    (hD0 : ∀ i, D i i = 0) :
    ∃ C E : Matrix (BooleanInput t) (BooleanInput t) K,
      OrderedMatchgateMatrix C ∧ OrderedMatchgateMatrix E ∧ C * E = 1 ∧ E * C = 1 ∧
      ∀ z, C (fun _ => 0) z = principalPfaffian D (booleanSubsetEquiv t z) := by
  let C := gaussianOrderedMatrix 0 (1 : Matrix (Fin t) (Fin t) K) (-D)
  have hn : ∀ i j, (-D) i j = -(-D) j i := by
    intro i j
    simpa using congrArg Neg.neg (hD i j)
  have hC : OrderedMatchgateMatrix C :=
    gaussianOrderedMatrix_isMatchgate _ _ _ (by simp) hn (by simp) (by simpa using hD0)
  have hr : C.rank = Fintype.card (BooleanInput t) :=
    gaussianOrderedMatrix_identity_cross_rank (-D) hn
  obtain ⟨E, hCE⟩ := exists_baseDecoder C (transpose_injective_of_rank_eq_card C hr)
  have hEC : E * C = 1 := mul_eq_one_comm.mp hCE
  exact ⟨C, E, hC, hC.leftInverse hEC, hCE, hEC,
    gaussianOrderedMatrix_vacuum_row D hD⟩
end Field

end
end MatchgateWidth
