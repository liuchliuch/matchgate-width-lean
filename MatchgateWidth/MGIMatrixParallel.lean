import MatchgateWidth.MGICyclicRotation
import MatchgateWidth.MGIPrefixTransform
import MatchgateWidth.ExactStarLowerBound

/-! # Parallel composition of ordered matchgate matrices
Two cyclic cuts nest the two boundary blocks in the ordinary matrix convention.
No unsigned arbitrary block permutation is asserted.
-/
namespace MatchgateWidth
noncomputable section
variable {K : Type*} [Field K]

theorem BooleanMatchgateIdentities.tensor {m n : ℕ}
    {F : BooleanTable m K} {G : BooleanTable n K}
    (hF : BooleanMatchgateIdentities F) (hG : BooleanMatchgateIdentities G) :
    BooleanMatchgateIdentities (fun z : BooleanInput (m+n) =>
      F (fun i => z (Fin.castAdd n i)) * G (fun j => z (Fin.natAdd m j))) := by
  have h := MatchgateIdentities.consecutiveTensor hF hG
  change MatchgateIdentities _
  convert h using 1
  funext S
  simp [consecutiveTensor, booleanSubsetEquiv, firstBlock, secondBlock]

/-- Ordinary ordered Kronecker composition, with independent bit words. -/
def orderedMatrixParallel {r t u v : ℕ}
    (P : Matrix (BooleanInput r) (BooleanInput t) K)
    (Q : Matrix (BooleanInput u) (BooleanInput v) K) :
    Matrix (BooleanInput (r+u)) (BooleanInput (t+v)) K :=
  fun x y => P (fun i => x (Fin.castAdd u i)) (fun j => y (Fin.castAdd v j)) *
    Q (fun i => x (Fin.natAdd r i)) (fun j => y (Fin.natAdd t j))

private theorem flip_val_left {m n : ℕ} (i : Fin (m+n)) (hi : i.val < m) :
    (finAddFlip i).val = n + i.val := by
  have he : i = ⟨i.val, i.isLt⟩ := rfl
  rw [he, finAddFlip_apply_mk_left hi]

private theorem flip_val_right {m n : ℕ} (i : Fin (m+n)) (hi : m ≤ i.val) :
    (finAddFlip i).val = i.val - m := by
  have he : i = ⟨i.val, i.isLt⟩ := rfl
  rw [he, finAddFlip_apply_mk_right hi]

/-- Parallel composition uses ordinary products, with exactly the reversed
combined output boundary prescribed by the matrix convention. -/
theorem OrderedMatchgateMatrix.parallel {r t u v : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    {Q : Matrix (BooleanInput u) (BooleanInput v) K}
    (hP : OrderedMatchgateMatrix P) (hQ : OrderedMatchgateMatrix Q) :
    OrderedMatchgateMatrix (orderedMatrixParallel P Q) := by
  have h1 := hP.rotateBlocks.tensor hQ
  have h2 := h1.cast (show (t+r)+(u+v) = t+(r+(u+v)) by omega)
  have h3 := h2.rotateBlocks
  have h4 := h3.cast (show (r+(u+v))+t = (r+u)+(t+v) by omega)
  change BooleanMatchgateIdentities _
  convert h4 using 1
  funext z
  simp only [orderedMatrixSignature, orderedMatrixParallel, castBooleanTable,
    Function.comp_apply]
  congr 1
  · congr 1
    · funext i
      congr 1
      apply Fin.ext
      simp only [Fin.val_castAdd,  Fin.val_cast, finAddFlip_apply_castAdd]
      rw [flip_val_right _ (by simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] <;> omega)]
      simp
    · funext j
      congr 1
      apply Fin.ext
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast, finAddFlip_apply_natAdd,
        Fin.val_rev]
      rw [flip_val_left _ (by simp only [Fin.val_cast, Fin.val_castAdd,  Fin.val_rev] <;> omega)]
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_rev]
      omega
  · congr 1
    · funext i
      congr 1
      apply Fin.ext
      simp only [Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast]
      rw [flip_val_right _ (by simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] <;> omega)]
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      omega
    · funext j
      congr 1
      apply Fin.ext
      simp only [ Fin.val_natAdd, Fin.val_cast, Fin.val_rev]
      rw [flip_val_right _ (by simp only [Fin.val_cast,  Fin.val_natAdd, Fin.val_rev] <;> omega)]
      simp only [Fin.val_cast,  Fin.val_natAdd, Fin.val_rev]
      omega

end
end MatchgateWidth
