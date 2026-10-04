import MatchgateWidth.RankTwoBlockReversal
import MatchgateWidth.ExactMatchgateLinear

/-! # Cyclic block supports are literal exact ordered matrix rowspaces -/
namespace MatchgateWidth
noncomputable section
open scoped Classical
set_option maxHeartbeats 600000

private theorem matrixBoundaryWord_independent_first {t s : ℕ}
    (x x' : BooleanInput t) (y : BooleanInput s) (v : Fin (t+s))
    (hv : ∀ k : Fin t, v ≠ Fin.castAdd s k) :
    matrixBoundaryWord x y v = matrixBoundaryWord x' y v := by
  induction v using Fin.addCases with
  | left k => exact (hv k rfl).elim
  | right k => simp [matrixBoundaryWord]

/-- A rerooting coordinate map preserving the entire selected block produces
a matrix whose rows are precisely the actual complementary-port slices. -/
theorem rerooted_matrix_rowSpace {n t s : ℕ}
    (G : (Fin n → BooleanInput t) → ℂ) (j : Fin n)
    (e : (Fin n × Fin t) ≃ Fin (t+s))
    (he : ∀ k, e (j,k) = Fin.castAdd s k) :
    orderedRowSpace (boundaryMatrix (fun z => G (fun i k => z (e (i,k))))).transpose =
      columnSupport (portFlatten G j) := by
  classical
  let W (x : BooleanInput t) (y : BooleanInput s) : Fin n → BooleanInput t :=
    fun i k => matrixBoundaryWord x y (e (i,k))
  have hfirst (x : BooleanInput t) (y : BooleanInput s) : W x y j = x := by
    funext k
    simp [W, he, matrixBoundaryWord]
  have hother (x x' : BooleanInput t) (y : BooleanInput s) (i : Fin n) (hi : i ≠ j) :
      W x y i = W x' y i := by
    funext k
    apply matrixBoundaryWord_independent_first
    intro l hh
    have hij := congrArg Prod.fst (e.injective (hh.trans (he l).symm))
    exact hi hij
  have hforward (y : BooleanInput s) :
      ∃ a : {i : Fin n // i ≠ j} → BooleanInput t,
      (fun x => G (W x y)) = fun x => G (insertBoundaryCoordinate j x a) := by
    refine ⟨fun i => W 0 y i, ?_⟩
    funext x
    apply congrArg G
    funext i
    by_cases hi : i = j
    · subst i
      simp only [hfirst, insertBoundaryCoordinate_same]
    · rw [insertBoundaryCoordinate_ne j x _ i hi]
      exact hother x 0 y i hi
  have hbackward (a : {i : Fin n // i ≠ j} → BooleanInput t) :
      ∃ y : BooleanInput s,
      (fun x => G (insertBoundaryCoordinate j x a)) = fun x => G (W x y) := by
    let z : Fin n → BooleanInput t := insertBoundaryCoordinate j 0 a
    let y : BooleanInput s := fun h => z (e.symm (Fin.natAdd t h.rev)).1 (e.symm (Fin.natAdd t h.rev)).2
    refine ⟨y, ?_⟩
    funext x
    apply congrArg G
    funext i k
    by_cases hi : i = j
    · subst i
      rw [insertBoundaryCoordinate_same, hfirst]
    · rw [insertBoundaryCoordinate_ne j x _ i hi]
      have hn (l : Fin t) : e (i,k) ≠ Fin.castAdd s l := by
        intro hh
        exact hi (congrArg Prod.fst (e.injective (hh.trans (he l).symm)))
      have hex : ∃ h : Fin s, e (i,k) = Fin.natAdd t h := by
        generalize hv : e (i,k) = v at *
        induction v using Fin.addCases with
        | left l => exact (hn l rfl).elim
        | right h => exact ⟨h, rfl⟩
      obtain ⟨h, hh⟩ := hex
      have hei : e.symm (Fin.natAdd t h) = (i,k) := by rw [← hh]; simp
      simp only [W, hh, matrixBoundaryWord, Fin.append_right, Fin.rev_rev, y, hei]
      exact (congrFun (insertBoundaryCoordinate_ne j (0 : BooleanInput t) a i hi) k).symm
  rw [orderedRowSpace, columnSupport, Matrix.range_mulVecLin]
  apply congrArg (Submodule.span ℂ)
  apply Set.ext
  intro u
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := hforward y
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨y, hy⟩ := hbackward a
    exact ⟨y, hy.symm⟩

/-- A scalar cyclic cut at the beginning of the selected block retains its
internal wire order and puts the entire block first. -/
theorem exists_cyclic_block_reroot {n t : ℕ} (j : Fin n) :
    ∃ e : (Fin n × Fin t) ≃ Fin (t + (n-1)*t),
      (∀ k, e (j,k) = Fin.castAdd ((n-1)*t) k) ∧
      ∀ F : BooleanTable (n*t) ℂ, BooleanMatchgateIdentities F →
        BooleanMatchgateIdentities
          (fun z => F (flattenBooleanBlocks (fun i k => z (e (i,k))))) := by
  have hj : j.val ≤ n := Nat.le_of_lt j.isLt
  have hn : 1 ≤ n := by omega
  have hs : n*t = j.val*t + (n-j.val)*t := by
    have h := Nat.add_sub_of_le hj
    nlinarith [Nat.sub_add_cancel hj]
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
  · intro F hF
    have h := (hF.cast hs).rotateBlocks.cast hr
    convert h using 1
    funext z
    apply congrArg F
    funext i
    simp only [ Function.comp_apply, flattenBooleanBlocks,
      e, Equiv.trans_apply, finCongr_apply]
    congr 1
    exact congrArg (fun q => Fin.cast hr (finAddFlip (Fin.cast hs q)))
      (finProdFinEquiv.apply_symm_apply i)

/-- Every actual consecutive block of an exact tensor is the literal rowspace
of an exact ordered matchgate matrix after cyclic rerooting and transpose.
There is no rank or nonzero hypothesis, and width zero is covered. -/
theorem BooleanMatchgateIdentities.exists_block_rowSpace {n t : ℕ}
    {F : BooleanTable (n*t) ℂ} (hF : BooleanMatchgateIdentities F) (j : Fin n) :
    ∃ A : Matrix (BooleanInput ((n-1)*t)) (BooleanInput t) ℂ,
      OrderedMatchgateMatrix A ∧ orderedRowSpace A =
        columnSupport (portFlatten (fun x => F (flattenBooleanBlocks x)) j) := by
  obtain ⟨e, he, hrot⟩ := exists_cyclic_block_reroot (t := t) j
  let G : BooleanTable (t+(n-1)*t) ℂ :=
    fun z => F (flattenBooleanBlocks (fun i k => z (e (i,k))))
  have hG : BooleanMatchgateIdentities G := hrot F hF
  have hA : OrderedMatchgateMatrix (boundaryMatrix G) := by
    change BooleanMatchgateIdentities _
    rwa [orderedMatrixSignature_boundaryMatrix]
  exact ⟨(boundaryMatrix G).transpose, hA.transpose,
    rerooted_matrix_rowSpace (fun x => F (flattenBooleanBlocks x)) j e he⟩

/-- Source geometric formulation: the output is an actual exact graph
matchgate matrix in the established input/output boundary convention. -/
theorem ExactMatchgate.exists_block_rowSpace {n t : ℕ}
    {F : BooleanTable (n*t) ℂ} (hF : ExactMatchgate F) (j : Fin n) :
    ∃ A : Matrix (BooleanInput ((n-1)*t)) (BooleanInput t) ℂ,
      ExactMatchgateMatrix A ∧ orderedRowSpace A =
        columnSupport (portFlatten (fun x => F (flattenBooleanBlocks x)) j) := by
  obtain ⟨A, hA, hrow⟩ := hF.matchgateIdentities.exists_block_rowSpace j
  exact ⟨A, hA.exactMatrix, hrow⟩

end
end MatchgateWidth
