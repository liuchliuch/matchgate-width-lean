import MatchgateWidth.MGIMatrixInverse
import MatchgateWidth.BaseDecoder

/-!
# Exact ordered decoders from pinned square minors

An increasing choice of physical output modes, with an arbitrary pinned XOR
pattern, induces an exact matchgate coordinate inclusion.  Whenever the
corresponding square restriction is nonsingular, its inverse composes with
that inclusion to give an exact right decoder.  No canonical-form assumption
is made in this interface.
-/

namespace MatchgateWidth
noncomputable section
open scoped symmDiff

/-- Keep the whole first block and embed the second block in increasing order. -/
def outputBoundaryEmbedding {m r t : ℕ} (e : Fin r ↪ Fin t) :
    Fin (m + r) ↪ Fin (m + t) where
  toFun := Fin.addCases (Fin.castAdd t) (fun i => Fin.natAdd m (e i))
  inj' := by
    intro i j h
    induction i using Fin.addCases with
    | left i =>
      induction j using Fin.addCases with
      | left j => simpa using h
      | right j =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
    | right i =>
      induction j using Fin.addCases with
      | left j =>
        simp only [Fin.addCases_left, Fin.addCases_right] at h
        have hv := congrArg Fin.val h
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      | right j =>
        simp only [Fin.addCases_right, Fin.natAdd_inj] at h
        simp [e.injective h]

@[simp] theorem outputBoundaryEmbedding_left {m r t : ℕ}
    (e : Fin r ↪ Fin t) (i : Fin m) :
    outputBoundaryEmbedding e (Fin.castAdd r i) = Fin.castAdd t i := by
  change Fin.addCases (motive := fun _ : Fin (m + r) => Fin (m + t))
    (Fin.castAdd t) (fun j => Fin.natAdd m (e j)) (Fin.castAdd r i) = _
  exact Fin.addCases_left i

@[simp] theorem outputBoundaryEmbedding_right {m r t : ℕ}
    (e : Fin r ↪ Fin t) (i : Fin r) :
    outputBoundaryEmbedding e (Fin.natAdd m i) = Fin.natAdd m (e i) := by
  change Fin.addCases (motive := fun _ : Fin (m + r) => Fin (m + t))
    (Fin.castAdd t) (fun j => Fin.natAdd m (e j)) (Fin.natAdd m i) = _
  exact Fin.addCases_right i

theorem outputBoundaryEmbedding_strictMono {m r t : ℕ}
    (e : Fin r ↪ Fin t) (he : StrictMono e) :
    StrictMono (outputBoundaryEmbedding (m := m) e) := by
  intro i j h
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simpa only [outputBoundaryEmbedding_left, Fin.lt_def, Fin.val_castAdd] using h
    | right j =>
      simp only [outputBoundaryEmbedding_left, outputBoundaryEmbedding_right]
      change i.val < m + (e j).val
      omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have : m + i.val < j.val := h
      omega
    | right j =>
      simp only [outputBoundaryEmbedding_right, Fin.natAdd_lt_natAdd_iff]
      exact he (by simpa using h)

@[simp] theorem firstBlock_map_outputBoundaryEmbedding {m r t : ℕ}
    (e : Fin r ↪ Fin t) (S : Finset (Fin (m + r))) :
    firstBlock (S.map (outputBoundaryEmbedding e)) = firstBlock S := by
  ext i
  simp only [mem_firstBlock, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, he⟩
    have hj' : j = Fin.castAdd r i := (outputBoundaryEmbedding e).injective
      (he.trans (outputBoundaryEmbedding_left e i).symm)
    simpa only [hj'] using hj
  · intro h
    exact ⟨Fin.castAdd r i, h, outputBoundaryEmbedding_left e i⟩

@[simp] theorem secondBlock_map_outputBoundaryEmbedding {m r t : ℕ}
    (e : Fin r ↪ Fin t) (S : Finset (Fin (m + r))) :
    secondBlock (S.map (outputBoundaryEmbedding e)) = (secondBlock S).map e := by
  ext i
  simp only [mem_secondBlock, Finset.mem_map, mem_secondBlock]
  constructor
  · rintro ⟨j, hj, hj'⟩
    induction j using Fin.addCases with
    | left j =>
      simp only [outputBoundaryEmbedding_left] at hj'
      have hv := congrArg Fin.val hj'
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    | right j =>
      exact ⟨j, hj, (Fin.natAdd_inj m).mp (by simpa only [outputBoundaryEmbedding_right] using hj')⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Fin.natAdd m j, hj, outputBoundaryEmbedding_right e j⟩

/-- Lift a Boolean output along an increasing physical-port embedding and
apply a fixed physical-output XOR pattern.  Disjointness is unnecessary:
selected bits in the pattern simply toggle the corresponding free modes. -/
def pinnedOutputWord {r t : ℕ} (e : Fin r ↪ Fin t)
    (p : Finset (Fin t)) (x : BooleanInput r) : BooleanInput t :=
  (booleanSubsetEquiv t).symm
    (reversePortSubset (((reversePortSubset ((booleanSubsetEquiv r) x)).map e) ∆ p))

/-- Restriction of columns to a pinned output-mode cube. -/
def pinnedOutputMatrix {m r t : ℕ} {R : Type*}
    (P : Matrix (BooleanInput m) (BooleanInput t) R)
    (e : Fin r ↪ Fin t) (p : Finset (Fin t)) :
    Matrix (BooleanInput m) (BooleanInput r) R :=
  P.submatrix id (pinnedOutputWord e p)

variable {R : Type*} [CommRing R]

/-- Pinning physical output modes preserves the exact ordered matrix class. -/
theorem OrderedMatchgateMatrix.pinnedOutput {m r t : ℕ}
    {P : Matrix (BooleanInput m) (BooleanInput t) R}
    (hP : OrderedMatchgateMatrix P) (e : Fin r ↪ Fin t)
    (he : StrictMono e) (p : Finset (Fin t)) :
    OrderedMatchgateMatrix (pinnedOutputMatrix P e p) := by
  rw [orderedMatchgateMatrix_iff] at hP ⊢
  have h := hP.ordered_pin (outputBoundaryEmbedding e)
    (outputBoundaryEmbedding_strictMono e he) (blockJoin ∅ p)
  convert h using 1
  funext S
  simp only [orderedMatrixSubsetSignature, pinnedOutputMatrix, Matrix.submatrix_apply,
    id_eq, pinnedOutputWord, Equiv.apply_symm_apply,
    reversePortSubset_reversePortSubset, firstBlock_symmDiff, secondBlock_symmDiff,
    firstBlock_map_outputBoundaryEmbedding, secondBlock_map_outputBoundaryEmbedding,
    firstBlock_blockJoin, secondBlock_blockJoin]
  rw [show firstBlock S ∆ ∅ = firstBlock S from symmDiff_bot _]

/-- The exact coordinate inclusion associated with a pinned output cube. -/
def pinnedOutputInclusion {r t : ℕ} (e : Fin r ↪ Fin t) (p : Finset (Fin t)) :
    Matrix (BooleanInput t) (BooleanInput r) R :=
  pinnedOutputMatrix 1 e p

@[simp] theorem pinnedOutputInclusion_apply {r t : ℕ}
    (e : Fin r ↪ Fin t) (p : Finset (Fin t))
    (y : BooleanInput t) (x : BooleanInput r) :
    pinnedOutputInclusion (R := R) e p y x =
      if y = pinnedOutputWord e p x then 1 else 0 := by
  simp [pinnedOutputInclusion, pinnedOutputMatrix, Matrix.one_apply]

theorem pinnedOutputInclusion_orderedMatchgate {r t : ℕ}
    (e : Fin r ↪ Fin t) (he : StrictMono e) (p : Finset (Fin t)) :
    OrderedMatchgateMatrix (pinnedOutputInclusion (R := R) e p) :=
  (OrderedMatchgateMatrix.one t).pinnedOutput e he p

@[simp] theorem mul_pinnedOutputInclusion {m r t : ℕ}
    (P : Matrix (BooleanInput m) (BooleanInput t) R)
    (e : Fin r ↪ Fin t) (p : Finset (Fin t)) :
    P * pinnedOutputInclusion e p = pinnedOutputMatrix P e p := by
  classical
  ext y x
  simp [Matrix.mul_apply, pinnedOutputInclusion_apply, pinnedOutputMatrix,
    Matrix.submatrix]

variable {K : Type*} [Field K]

/-- A nonsingular pinned output square gives a genuine exact ordered decoder.
The only extra input is the specified minor's determinant, not a decoder or
a matchgate canonical form. -/
theorem OrderedMatchgateMatrix.exists_rightInverse_of_pinned_det {r t : ℕ}
    {P : Matrix (BooleanInput r) (BooleanInput t) K}
    (hP : OrderedMatchgateMatrix P) (e : Fin r ↪ Fin t)
    (he : StrictMono e) (p : Finset (Fin t))
    (hdet : IsUnit (pinnedOutputMatrix P e p).det) :
    ∃ D : Matrix (BooleanInput t) (BooleanInput r) K,
      OrderedMatchgateMatrix D ∧ P * D = 1 := by
  let Q := pinnedOutputMatrix P e p
  refine ⟨pinnedOutputInclusion e p * Q⁻¹,
    (pinnedOutputInclusion_orderedMatchgate e he p).mul ((hP.pinnedOutput e he p).inv hdet), ?_⟩
  rw [← Matrix.mul_assoc, mul_pinnedOutputInclusion]
  exact Matrix.mul_nonsing_inv Q hdet

end
end MatchgateWidth
