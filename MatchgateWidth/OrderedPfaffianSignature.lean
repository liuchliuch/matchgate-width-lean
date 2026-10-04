import MatchgateWidth.PfaffianIdentities
import Mathlib.Data.List.OfFn

/-!
# Literal matchgate identities in an explicit boundary-list order

A duplicate-free exhaustive list fixes the Boolean port enumeration by its
positions. Filtering that same list is exactly the principal-Pfaffian chart of
the matrix pulled back along `List.get`. No permutation invariance of literal
matchgate identities is used.
-/

namespace MatchgateWidth

variable {I R : Type*} [CommRing R]

/-- Enumerate the labels in exactly the supplied list order. -/
noncomputable def orderedListEquiv (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) : Fin xs.length ≃ I :=
  Equiv.ofBijective xs.get ⟨List.nodup_iff_injective_get.mp hn, by
    intro i
    exact List.mem_iff_get.mp (hall i)⟩

@[simp] theorem orderedListEquiv_apply (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) (i : Fin xs.length) :
    orderedListEquiv xs hn hall i = xs.get i := rfl

/-- Boolean assignments indexed by list positions, transported to its labels.
The bit `1` corresponds to selecting a label in the Pfaffian filter. -/
noncomputable def orderedBooleanAssignment (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) : BooleanInput xs.length ≃ (I → Bool) where
  toFun z i := decide (z ((orderedListEquiv xs hn hall).symm i) = 1)
  invFun y i := if y (xs.get i) then 1 else 0
  left_inv z := by
    funext i
    simp only [← orderedListEquiv_apply xs hn hall i, Equiv.symm_apply_apply]
    generalize z i = b
    fin_cases b <;> rfl
  right_inv y := by
    funext i
    have h : xs.get ((orderedListEquiv xs hn hall).symm i) = i :=
      (orderedListEquiv xs hn hall).apply_symm_apply i
    simp only [h]
    cases y i <;> rfl

@[simp] theorem orderedBooleanAssignment_get (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) (z : BooleanInput xs.length) (i : Fin xs.length) :
    orderedBooleanAssignment xs hn hall z (xs.get i) = decide (z i = 1) := by
  change decide (z ((orderedListEquiv xs hn hall).symm
    (orderedListEquiv xs hn hall i)) = 1) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem orderedBooleanAssignment_symm_apply (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) (y : I → Bool) (i : Fin xs.length) :
    (orderedBooleanAssignment xs hn hall).symm y i =
      if y (xs.get i) then 1 else 0 := rfl

/-- The increasing selected positions are the filter of the full position list. -/
theorem pfaffianSelectedPorts_eq_filter_finRange {s : ℕ} (z : BooleanInput s) :
    pfaffianSelectedPorts z = (List.finRange s).filter (fun i => decide (z i = 1)) := by
  apply (pfaffianSelectedPorts_sorted z).eq_of_mem_iff
    (((List.sortedLT_finRange s).pairwise.filter _).sortedLT)
  intro i
  simp

/-- Filtering the actual boundary list preserves exactly its positional order. -/
theorem orderedBooleanAssignment_filter (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) (z : BooleanInput xs.length) :
    xs.filter (orderedBooleanAssignment xs hn hall z) =
      (pfaffianSelectedPorts z).map xs.get := by
  rw [pfaffianSelectedPorts_eq_filter_finRange]
  have hfun : (orderedBooleanAssignment xs hn hall z ∘ xs.get) =
      (fun i => decide (z i = 1)) := by
    funext i
    exact orderedBooleanAssignment_get xs hn hall z i
  rw [← hfun, ← List.filter_map, List.map_get_finRange]

/-- The actual filtered-list signature equals the principal Pfaffian in the
explicit position-indexed matrix. -/
theorem orderedPfaffianSignature_eq (xs : List I) (hn : xs.Nodup)
    (hall : ∀ i, i ∈ xs) (A : Matrix I I R) (c : R)
    (z : BooleanInput xs.length) :
    c * pfaffianList A (xs.filter (orderedBooleanAssignment xs hn hall z)) =
      c * principalPfaffian (A.submatrix xs.get xs.get)
        (booleanSubsetEquiv xs.length z) := by
  rw [orderedBooleanAssignment_filter, pfaffianList_map]
  rfl

/-- An actual scaled Pfaffian signature satisfies the literal Boolean matchgate
identities when the Boolean coordinates enumerate its fixed boundary list. -/
theorem orderedPfaffianSignature_booleanMatchgateIdentities
    (xs : List I) (hn : xs.Nodup) (hall : ∀ i, i ∈ xs)
    (A : Matrix I I R) (hskew : ∀ i j, A i j = -A j i)
    (hdiag : ∀ i, A i i = 0) (c : R) :
    BooleanMatchgateIdentities (fun z =>
      c * pfaffianList A (xs.filter (orderedBooleanAssignment xs hn hall z))) := by
  have h := (principalPfaffian_matchgateIdentities (A.submatrix xs.get xs.get)
    (fun i j => hskew (xs.get i) (xs.get j))
    (fun i => hdiag (xs.get i))).const_mul c
  unfold BooleanMatchgateIdentities
  simpa only [orderedPfaffianSignature_eq, Equiv.apply_symm_apply] using h

end MatchgateWidth
