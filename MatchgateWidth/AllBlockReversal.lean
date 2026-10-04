import MatchgateWidth.BlockSupportExtraction
import MatchgateWidth.AllLeftSupportExtraction
import MatchgateWidth.BinaryLiftMatrix

/-! # Independent rank-two block reversals of exact local signatures -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

/-- Cyclic rerooting is an equivalence on MGI, not just a forward closure. -/
theorem BooleanMatchgateIdentities.rotateBlocks_iff {m n : ℕ} (F : BooleanTable (m+n) ℂ) :
    BooleanMatchgateIdentities F ↔ BooleanMatchgateIdentities
      (fun z : BooleanInput (n+m) => F (fun i => z (finAddFlip i))) := by
  constructor
  · exact fun h => h.rotateBlocks
  · intro h
    have hh := h.rotateBlocks
    convert hh using 1
    funext z
    apply congrArg F
    funext i
    induction i using Fin.addCases <;> simp

/-- Equality casts retain the same ordered MGI predicate in both directions. -/
theorem BooleanMatchgateIdentities.cast_iff {m n : ℕ} (h : m = n) (F : BooleanTable m ℂ) :
    BooleanMatchgateIdentities (castBooleanTable h F) ↔ BooleanMatchgateIdentities F := by
  cases h
  rfl

/-- The literal scalar cyclic reroot preserves and reflects MGI. -/
theorem exists_cyclic_block_reroot_iff {n t : ℕ} (j : Fin n) :
    ∃ e : (Fin n × Fin t) ≃ Fin (t + (n-1)*t),
      (∀ k, e (j,k) = Fin.castAdd ((n-1)*t) k) ∧
      ∀ F : BooleanTable (n*t) ℂ, BooleanMatchgateIdentities F ↔
        BooleanMatchgateIdentities
          (fun z => F (flattenBooleanBlocks (fun i k => z (e (i,k))))) := by
  have hj : j.val ≤ n := Nat.le_of_lt j.isLt
  have hn : 1 ≤ n := by omega
  have hs : n*t = j.val*t + (n-j.val)*t := by nlinarith [Nat.sub_add_cancel hj]
  have hr : (n-j.val)*t + j.val*t = t + (n-1)*t := by
    nlinarith [Nat.sub_add_cancel hj, Nat.sub_add_cancel hn]
  let e : (Fin n × Fin t) ≃ Fin (t+(n-1)*t) :=
    finProdFinEquiv.trans ((finCongr hs).trans (finAddFlip.trans (finCongr hr)))
  refine ⟨e, ?_, ?_⟩
  · intro k
    have ht : t ≤ (n-j.val)*t := by
      have : 1 ≤ n-j.val := by omega
      nlinarith
    let k' : Fin ((n-j.val)*t) := Fin.castLE ht k
    have hk : (finCongr hs) (finProdFinEquiv (j,k)) = Fin.natAdd (j.val*t) k' := by
      apply Fin.ext
      change k.val + t * j.val = j.val * t + k.val
      ring
    change Fin.cast hr (finAddFlip ((finCongr hs) (finProdFinEquiv (j,k)))) = _
    rw [hk, finAddFlip_apply_natAdd]
    apply Fin.ext
    rfl
  · intro F
    have heq : (fun z => F (flattenBooleanBlocks (fun i k => z (e (i,k))))) =
        castBooleanTable hr (fun z => castBooleanTable hs F (fun i => z (finAddFlip i))) := by
      funext z
      apply congrArg F
      funext i
      simp only [ Function.comp_apply, flattenBooleanBlocks,
        e, Equiv.trans_apply, finCongr_apply]
      congr 1
      exact congrArg (fun q => Fin.cast hr (finAddFlip (Fin.cast hs q)))
        (finProdFinEquiv.apply_symm_apply i)
    rw [heq, BooleanMatchgateIdentities.cast_iff,
      ← BooleanMatchgateIdentities.rotateBlocks_iff, BooleanMatchgateIdentities.cast_iff]

@[simp] theorem blockCoordinates_flatten {n t : ℕ} (x : Fin n → BooleanInput t) :
    (booleanBlocksEquiv n t).symm (flattenBooleanBlocks x) = x := by
  ext i k
  simp [booleanBlocksEquiv, flattenBooleanBlocks]

/-- Reverse one word internally, with no permutation of its block. -/
def reverseBlockWord {t : ℕ} (x : BooleanInput t) : BooleanInput t := fun i => x i.rev

@[simp] theorem reverseBlockWord_involutive {t : ℕ} (x : BooleanInput t) :
    reverseBlockWord (reverseBlockWord x) = x := by ext i; simp [reverseBlockWord]

/-- Reverse precisely one complete consecutive block in a local tensor. -/
def reverseTensorBlock {n t : ℕ} (F : BooleanTable (n*t) ℂ) (j : Fin n) :
    BooleanTable (n*t) ℂ := fun z => F (flattenBooleanBlocks
      (Function.update ((booleanBlocksEquiv n t).symm z) j
        (reverseBlockWord ((booleanBlocksEquiv n t).symm z j))))

/-- Rank-at-most-two makes the otherwise unjustified single-block reversal an
actual exact MGI operation. The selected block can occur anywhere in the cyclic
boundary; no arbitrary permutation or orientation closure is assumed. -/
theorem BooleanMatchgateIdentities.reverse_tensor_block {n t : ℕ}
    {F : BooleanTable (n*t) ℂ} (hF : BooleanMatchgateIdentities F) (j : Fin n)
    (hr : Module.finrank ℂ (columnSupport
      (portFlatten (fun x => F (flattenBooleanBlocks x)) j)) ≤ 2) :
    BooleanMatchgateIdentities (reverseTensorBlock F j) := by
  obtain ⟨e, he, hiff⟩ := exists_cyclic_block_reroot_iff (t := t) j
  let R : BooleanTable (t+(n-1)*t) ℂ :=
    fun z => F (flattenBooleanBlocks (fun i k => z (e (i,k))))
  have hR : BooleanMatchgateIdentities R := (hiff F).mp hF
  have hrow := rerooted_matrix_rowSpace (fun x => F (flattenBooleanBlocks x)) j e he
  have hPr : (boundaryMatrix R).rank ≤ 2 := by
    rw [← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℂ (orderedRowSpace (boundaryMatrix R).transpose) ≤ 2
    rw [hrow]
    exact hr
  have hrev := hR.reverse_first_block_of_rank_le_two hPr
  apply (hiff (reverseTensorBlock F j)).mpr
  convert hrev using 1
  funext z
  have hblocks : (booleanBlocksEquiv n t).symm
      (flattenBooleanBlocks (fun i k => z (e (i,k)))) = (fun i k => z (e (i,k))) :=
    blockCoordinates_flatten _
  simp only [reverseTensorBlock, hblocks, R]
  apply congrArg F
  apply congrArg flattenBooleanBlocks
  funext i k
  by_cases hi : i = j
  · subst i
    simp [he, reverseBlockWord]
  · rw [Function.update_of_ne hi]
    have hn (l : Fin t) : e (i,k) ≠ Fin.castAdd ((n-1)*t) l := by
      intro hh
      exact hi (congrArg Prod.fst (e.injective (hh.trans (he l).symm)))
    generalize hv : e (i,k) = v at *
    induction v using Fin.addCases with
    | left l => exact (hn l rfl).elim
    | right l => simp

/-- Reverse an arbitrary selected set of complete blocks, independently. -/
def reverseBlockAssignment {n t : ℕ} (s : Finset (Fin n))
    (x : Fin n → BooleanInput t) : Fin n → BooleanInput t :=
  fun i => if i ∈ s then reverseBlockWord (x i) else x i

def reverseTensorBlocks {n t : ℕ} (s : Finset (Fin n)) (F : BooleanTable (n*t) ℂ) :
    BooleanTable (n*t) ℂ := fun z => F (flattenBooleanBlocks
      (reverseBlockAssignment s ((booleanBlocksEquiv n t).symm z)))

@[simp] theorem reverseTensorBlocks_blocks {n t : ℕ} (s : Finset (Fin n))
    (F : BooleanTable (n*t) ℂ) (x : Fin n → BooleanInput t) :
    reverseTensorBlocks s F (flattenBooleanBlocks x) =
      F (flattenBooleanBlocks (reverseBlockAssignment s x)) := by
  unfold reverseTensorBlocks
  change F (flattenBooleanBlocks (reverseBlockAssignment s
    ((booleanBlocksEquiv n t).symm ((booleanBlocksEquiv n t) x)))) = _
  rw [Equiv.symm_apply_apply]

/-- Separate coordinate reversals only permute rows and columns of each true
whole-block flattening. Hence its rank cannot increase. -/
theorem reverseTensorBlocks_port_rank_le {n t : ℕ} (s : Finset (Fin n))
    (F : BooleanTable (n*t) ℂ) (j : Fin n) :
    Module.finrank ℂ (columnSupport (portFlatten
      (fun x => reverseTensorBlocks s F (flattenBooleanBlocks x)) j)) ≤
    Module.finrank ℂ (columnSupport (portFlatten (fun x => F (flattenBooleanBlocks x)) j)) := by
  let rowMap : BooleanInput t → BooleanInput t := fun x => if j ∈ s then reverseBlockWord x else x
  let colMap : ({i : Fin n // i ≠ j} → BooleanInput t) →
      ({i : Fin n // i ≠ j} → BooleanInput t) :=
    fun a i => if i.val ∈ s then reverseBlockWord (a i) else a i
  have he : portFlatten (fun x => reverseTensorBlocks s F (flattenBooleanBlocks x)) j =
      (portFlatten (fun x => F (flattenBooleanBlocks x)) j).submatrix rowMap colMap := by
    ext x a
    simp only [portFlatten, reverseTensorBlocks_blocks, Matrix.submatrix_apply]
    apply congrArg F
    apply congrArg flattenBooleanBlocks
    funext i
    by_cases hi : i = j
    · subst i
      simp [reverseBlockAssignment, rowMap]
    · simp [reverseBlockAssignment, 
        colMap, hi]
  change (portFlatten (fun x => reverseTensorBlocks s F (flattenBooleanBlocks x)) j).rank ≤ _
  rw [he]
  exact Matrix.rank_submatrix_le _ rowMap colMap

@[simp] theorem reverseTensorBlocks_empty {n t : ℕ} (F : BooleanTable (n*t) ℂ) :
    reverseTensorBlocks ∅ F = F := by
  ext z
  unfold reverseTensorBlocks
  have he : reverseBlockAssignment (t := t) (∅ : Finset (Fin n)) = id := by
    funext x i
    simp [reverseBlockAssignment]
  rw [he]
  exact congrArg F ((booleanBlocksEquiv n t).apply_symm_apply z)

theorem reverseTensorBlocks_insert {n t : ℕ} (s : Finset (Fin n)) (j : Fin n)
    (hj : j ∉ s) (F : BooleanTable (n*t) ℂ) :
    reverseTensorBlocks (insert j s) F = reverseTensorBlock (reverseTensorBlocks s F) j := by
  ext z
  simp only [reverseTensorBlock, reverseTensorBlocks, blockCoordinates_flatten]
  apply congrArg F
  apply congrArg flattenBooleanBlocks
  funext i
  by_cases hi : i = j
  · subst i
    simp [reverseBlockAssignment, hj]
  · simp [reverseBlockAssignment, hi]

/-- Any number of rank-two complete blocks can be reversed. Every intermediate
rank bound is proved from its actual permuted flattening. -/
theorem BooleanMatchgateIdentities.reverse_tensor_blocks {n t : ℕ}
    {F : BooleanTable (n*t) ℂ} (hF : BooleanMatchgateIdentities F)
    (hr : ∀ j, Module.finrank ℂ (columnSupport
      (portFlatten (fun x => F (flattenBooleanBlocks x)) j)) ≤ 2)
    (s : Finset (Fin n)) : BooleanMatchgateIdentities (reverseTensorBlocks s F) := by
  induction s using Finset.induction_on with
  | empty => simpa only [reverseTensorBlocks_empty] using hF
  | @insert j s hj ih =>
    rw [reverseTensorBlocks_insert s j hj]
    exact ih.reverse_tensor_block j ((reverseTensorBlocks_port_rank_le s F j).trans (hr j))

/-- The exact ordered matrix rank theorem excludes rank three. -/
theorem OrderedMatchgateMatrix.rank_le_two_of_le_three {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) ℂ}
    (hP : OrderedMatchgateMatrix P) (hr : P.rank ≤ 3) : P.rank ≤ 2 := by
  rcases hP.rank_zero_or_power with hz | ⟨k,hk⟩
  · omega
  · have hk1 : k ≤ 1 := by
      by_contra hn
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 2 ≤ k by omega)
      rw [← hk] at hp
      norm_num at hp
      omega
    rcases (show k=0 ∨ k=1 by omega) with rfl | rfl <;> norm_num at hk ⊢ <;> omega

/-- Every exact qutrit left lift has deficient whole-block supports. This
follows from rank at most three and exact matchgate power-of-two rank. -/
theorem exact_qutrit_lift_block_rank_le_two {n t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (T : (Fin n → Fin 3) → ℂ) (hT : ExactMatchgate (leftBooleanLift M n T)) (j : Fin n) :
    Module.finrank ℂ (columnSupport (portFlatten
      (fun x => leftBooleanLift M n T (flattenBooleanBlocks x)) j)) ≤ 2 := by
  obtain ⟨A,hA,hrow⟩ := hT.exists_block_rowSpace j
  obtain ⟨B,hB,hspace⟩ := exact_lift_block_rowSpace M hM T hT j
  have hroweq : orderedRowSpace A = orderedRowSpace B := by
    have he : (fun x => leftBooleanLift M n T (flattenBooleanBlocks x)) = leftTransform M T := by
      funext x
      unfold leftBooleanLift
      change leftTransform M T ((booleanBlocksEquiv n t).symm ((booleanBlocksEquiv n t) x)) = _
      rw [Equiv.symm_apply_apply]
    rw [hrow, hspace, he, transformed_port_support_of_full_row_rank M (by simpa using hM)]
  have hrB : B.rank ≤ 3 := by
    rw [Matrix.rank_eq_finrank_span_row]
    change Module.finrank ℂ (orderedRowSpace B) ≤ 3
    rw [hspace, finrank_map_transpose_eq M (transpose_injective_of_rank_eq_card M (by simpa using hM))]
    change (portFlatten T j).rank ≤ 3
    simpa using Matrix.rank_le_card_height (portFlatten T j)
  rw [← hrow, hroweq]
  change Module.finrank ℂ (Submodule.span ℂ (Set.range B.row)) ≤ 2
  rw [← Matrix.rank_eq_finrank_span_row]
  exact hB.identities.rank_le_two_of_le_three hrB

/-- The source local correction: reverse every left block before inserting its
exact graph into oppositely oriented physical ribbons. This is proved valid,
including zero tensors, zero width and nullary tensors. -/
theorem exact_qutrit_lift_reverse_all_blocks {n t : ℕ}
    (M : Matrix (Fin 3) (BooleanInput t) ℂ) (hM : M.rank = 3)
    (T : (Fin n → Fin 3) → ℂ) (hT : ExactMatchgate (leftBooleanLift M n T)) :
    ExactMatchgate (reverseTensorBlocks Finset.univ (leftBooleanLift M n T)) :=
  (hT.matchgateIdentities.reverse_tensor_blocks
    (exact_qutrit_lift_block_rank_le_two M hM T hT) Finset.univ).exactMatchgate

end
end MatchgateWidth
