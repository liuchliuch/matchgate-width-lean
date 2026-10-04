import MatchgateWidth.BlockInterpolationOrder
import MatchgateWidth.OrderedPfaffianSignature

/-! # Position-indexed interpolation with the exact repeated boundary word -/
namespace MatchgateWidth
noncomputable section

def interpolationBoundaryOrder (k : ℕ) : List (InterpolationMode k) :=
  blockMajorModes (Finset.univ : Finset (Fin k))

theorem interpolationBoundaryOrder_length (k : ℕ) :
    (interpolationBoundaryOrder k).length = k * 2 ^ k := by
  simp [interpolationBoundaryOrder, blockMajorModes_eq_logicalBlocks,
    List.length_flatMap, logicalModeBlock_length]

def interpolationRepetitionBits {k : ℕ} (x : Fin k → Bool) :
    BooleanInput (interpolationBoundaryOrder k).length :=
  fun i => if x (incidencePort ((interpolationBoundaryOrder k).get i).1) then 1 else 0

theorem interpolationRepetitionBits_word {k : ℕ} (x : Fin k → Bool) :
    List.ofFn (fun i => decide (interpolationRepetitionBits x i = 1)) =
      booleanRepetitionWord x := by
  have h := blockMajorModes_repetitionWord x
  rw [← h]
  change List.ofFn _ = (interpolationBoundaryOrder k).map _
  conv_rhs => rw [← List.map_get_finRange (interpolationBoundaryOrder k)]
  simp only [List.map_map, Function.comp_def]
  rw [List.ofFn_eq_map]
  congr 1
  funext i
  simp [interpolationRepetitionBits]

/-- The named matrix is pulled back along the full physical boundary order. -/
def interpolationPositionMatrix {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) :
    Matrix (Fin (interpolationBoundaryOrder k).length)
      (Fin (interpolationBoundaryOrder k).length) K :=
  (tableInterpolationMatrix f hf).submatrix
    (interpolationBoundaryOrder k).get (interpolationBoundaryOrder k).get

theorem interpolationPositionMatrix_skew {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) :
    ∀ i j, interpolationPositionMatrix f hf i j = -interpolationPositionMatrix f hf j i :=
  fun i j => interpolationMatrix_skew _ _ _

theorem interpolationPositionMatrix_diag {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) :
    ∀ i, interpolationPositionMatrix f hf i i = 0 :=
  fun i => interpolationMatrix_diag _ _

theorem interpolationPositionMatrix_repetition {k : ℕ} {K : Type*} [Field K]
    (f : Finset (Fin k) → K) (hf : ∀ T, f T ≠ 0) (x : Fin k → Bool) :
    principalPfaffian (interpolationPositionMatrix f hf)
      (booleanSubsetEquiv _ (interpolationRepetitionBits x)) =
      f (Finset.univ.filter fun i => x i) / f ∅ := by
  let xs := interpolationBoundaryOrder k
  have hn : xs.Nodup := fullBlockMajorModes_nodup k
  have hall : ∀ m, m ∈ xs := mem_fullBlockMajorModes
  have h := orderedPfaffianSignature_eq xs hn hall (tableInterpolationMatrix f hf) 1
    (interpolationRepetitionBits x)
  simp only [one_mul] at h
  have hbits : orderedBooleanAssignment xs hn hall (interpolationRepetitionBits x) =
      (fun m => x (incidencePort m.1)) := by
    apply (orderedBooleanAssignment xs hn hall).symm.injective
    rw [Equiv.symm_apply_apply]
    rfl
  rw [hbits] at h
  change principalPfaffian ((tableInterpolationMatrix f hf).submatrix xs.get xs.get) _ = _
  rw [← h]
  change pfaffianList _ ((blockMajorModes (Finset.univ : Finset (Fin k))).filter _) = _
  rw [blockMajorModes_booleanSelection]
  exact tableInterpolationMatrix_blockMajor f hf _

end
end MatchgateWidth
