import MatchgateWidth.SignedCliffordAction
import MatchgateWidth.MGIMatrixComposition
import MatchgateWidth.MGIOperations
import MatchgateWidth.MGICyclicRotation
import MatchgateWidth.PfaffianIdentities

/-! # Actual Clifford-vector matrices satisfy the ordered matchgate identities -/
namespace MatchgateWidth
noncomputable section
open scoped symmDiff
variable {R : Type*} [CommRing R] {n t : ℕ}

/-- Wedge multiplication by a boundary linear form, in ordered subset coordinates. -/
def boundaryWedge (v : Fin n → R) (F : SubsetSignature n R) : SubsetSignature n R :=
  fun S => ∑ i ∈ S, fermionSign S i * v i * F (S.erase i)

/-- A skew matrix with an additional initial boundary mode. -/
abbrev borderedSkew (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R :=
  Fin.cases (Fin.cases 0 v) (fun i => Fin.cases (-v i) (A i))

@[simp] theorem borderedSkew_zero_succ (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (i : Fin n) : borderedSkew v A 0 i.succ = v i := rfl
@[simp] theorem borderedSkew_succ_succ (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) : borderedSkew v A i.succ j.succ = A i j := rfl

theorem borderedSkew_skew (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i j, A i j = -A j i) : ∀ i j, borderedSkew v A i j = -borderedSkew v A j i := by
  intro i j
  induction i using Fin.cases <;> induction j using Fin.cases <;>
    simp only [borderedSkew, Fin.cases_zero, Fin.cases_succ, neg_zero, neg_neg]
  exact hA _ _

theorem borderedSkew_diag (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (hA : ∀ i, A i i = 0) : ∀ i, borderedSkew v A i i = 0 := by
  intro i
  induction i using Fin.cases <;> simp [borderedSkew, hA]

private theorem clifford_sort_pin (S : Finset (Fin n)) :
    (S.map (Fin.succEmb n) ∆ {0}).sort (· ≤ ·) =
      0 :: (S.sort (· ≤ ·)).map Fin.succ := by
  have h0 : (0 : Fin (n+1)) ∉ S.map (Fin.succEmb n) := by simp
  have hset : S.map (Fin.succEmb n) ∆ {0} = insert 0 (S.map (Fin.succEmb n)) := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
    by_cases hi : i = 0
    · subst i; simp [h0]
    · simp [hi]
  rw [hset, Finset.sort_insert (· ≤ ·) (fun i _ => Fin.zero_le i) h0]
  rw [← Finset.map_sort (Fin.succEmb n) S (· ≤ ·) (· ≤ ·)]
  · rfl
  · intro a _ b _
    exact Fin.succ_le_succ_iff.symm

/-- Pinning the extra mode is precisely exterior multiplication by the border. -/
theorem borderedSkew_pin (v : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin n)) :
    principalPfaffian (borderedSkew v A) (S.map (Fin.succEmb n) ∆ {0}) =
      boundaryWedge v (principalPfaffian A) S := by
  rw [principalPfaffian, clifford_sort_pin, pfaffianList]
  unfold boundaryWedge fermionSign
  simp only [mul_assoc]
  rw [← sum_sort_sign S (fun i => v i * principalPfaffian A (S.erase i))]
  apply Fintype.sum_equiv (finCongr (List.length_map _))
  intro j
  simp only [finCongr_apply, Fin.val_cast, Fin.getElem_fin, List.getElem_map, borderedSkew_zero_succ,
    List.eraseIdx_map, pfaffianList_map]
  change (-1 : R)^j.val * (v _ * pfaffianList A _) = _
  rw [principalPfaffian]
  have he := sort_erase_getElem S (j.cast (List.length_map _))
  simp only [Fin.getElem_fin, Fin.val_cast] at he
  rw [he]

theorem boundaryWedge_principalPfaffian_isMatchgate (v : Fin n → R)
    (A : Matrix (Fin n) (Fin n) R) (hA : ∀ i j, A i j = -A j i)
    (hA0 : ∀ i, A i i = 0) : MatchgateIdentities (boundaryWedge v (principalPfaffian A)) := by
  have h := (principalPfaffian_matchgateIdentities (borderedSkew v A)
    (borderedSkew_skew v A hA) (borderedSkew_diag v A hA0)).ordered_pin
    (Fin.succEmb n) (Fin.strictMono_succ) {0}
  simpa only [borderedSkew_pin] using h

/-- On a chart with nonzero vacuum, arbitrary exterior multiplication preserves MGI. -/
theorem MatchgateIdentities.boundaryWedge {K : Type*} [Field K]
    {F : SubsetSignature n K} (hF : MatchgateIdentities F) (h0 : F ∅ ≠ 0)
    (v : Fin n → K) : MatchgateIdentities (boundaryWedge v F) := by
  let A := pfaffianChartMatrix (mgiChartParameters F)
  have hrep (S : Finset (Fin n)) : F S = F ∅ * principalPfaffian A S := by
    simpa [principalPfaffian, A] using hF.eq_pfaffian_chart_on_list h0
      (S.sort (· ≤ ·)) (Finset.sortedLT_sort S)
  have h := (boundaryWedge_principalPfaffian_isMatchgate v A
    (fun i j => pfaffianChartMatrix_skew _ j i) (pfaffianChartMatrix_diag _)).const_mul (F ∅)
  have heq : MatchgateWidth.boundaryWedge v F = (fun S => F ∅ * MatchgateWidth.boundaryWedge v (principalPfaffian A) S) := by
    funext S
    simp only [MatchgateWidth.boundaryWedge, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hrep]
    ring
  rw [heq]
  exact h


private theorem clifford_xor_erase (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
    S ∆ {i} = S.erase i := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
  grind

theorem boundaryWedge_eq_sum (v : Fin n → R) (F : SubsetSignature n R)
    (S : Finset (Fin n)) :
    boundaryWedge v F S =
      ∑ i : Fin n, if i ∈ S then fermionSign S i * v i * F (S ∆ {i}) else 0 := by
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [clifford_xor_erase S i hi]

private theorem clifford_below_left {a b : ℕ} (A : Finset (Fin a)) (B : Finset (Fin b))
    (i : Fin a) : subsetBelow (blockJoin A B) (Fin.castAdd b i) = subsetBelow A i := by
  have heq : (blockJoin A B).filter (· < Fin.castAdd b i) =
      blockJoin (A.filter (· < i)) (∅ : Finset (Fin b)) := by
    ext j
    induction j using Fin.addCases with
    | left j =>
      simp only [Finset.mem_filter, ← mem_firstBlock, firstBlock_blockJoin]
      rfl
    | right j =>
      simp only [Finset.mem_filter, ← mem_secondBlock, secondBlock_blockJoin, Finset.notMem_empty, iff_false, not_and]
      intro _ h
      have := j.isLt
      have := i.isLt
      change a + j.val < i.val at h
      omega
  simp only [subsetBelow, heq, blockJoin_card, Finset.card_empty, add_zero]

private theorem clifford_below_right {a b : ℕ} (A : Finset (Fin a)) (B : Finset (Fin b))
    (i : Fin b) : subsetBelow (blockJoin A B) (Fin.natAdd a i) = A.card + subsetBelow B i := by
  have heq : (blockJoin A B).filter (· < Fin.natAdd a i) =
      blockJoin A (B.filter (· < i)) := by
    ext j
    induction j using Fin.addCases with
    | left j =>
      simp only [Finset.mem_filter, ← mem_firstBlock, firstBlock_blockJoin, and_iff_left_iff_imp]
      intro _
      have := j.isLt
      change j.val < a + i.val
      omega
    | right j => simp only [Finset.mem_filter, ← mem_secondBlock, secondBlock_blockJoin, Fin.natAdd_lt_natAdd_iff]
  simp only [subsetBelow, heq, blockJoin_card]

/-- The boundary linear form for the actual creation/contraction coefficients. -/
def cliffordBoundaryLinear (z : CliffordVector t R) : Fin (t+t) → R :=
  Fin.addCases z.1 (fun j => z.2 j.rev)

/-- The actual coefficient matrix of Clifford multiplication, target before source. -/
def signedCliffordMatrix (z : CliffordVector t R) :
    Matrix (BooleanInput t) (BooleanInput t) R := fun x y =>
  signedCliffordAction z (Pi.single (booleanSubsetEquiv t y) 1) (booleanSubsetEquiv t x)

theorem signedCliffordMatrix_apply (z : CliffordVector t R) (x y : BooleanInput t) :
    signedCliffordMatrix z x y = ∑ i : Fin t,
      fermionSign (booleanSubsetEquiv t x) i *
        (if i ∈ booleanSubsetEquiv t x then z.1 i else z.2 i) *
        (if booleanSubsetEquiv t x ∆ {i} = booleanSubsetEquiv t y then 1 else 0) := by
  simp only [signedCliffordMatrix, signedCliffordAction, LinearMap.sum_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
    Finset.sum_apply, smul_eq_mul, fermionCreate_apply, fermionContract_apply, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ booleanSubsetEquiv t x <;>
    by_cases he : booleanSubsetEquiv t x ∆ {i} = booleanSubsetEquiv t y <;>
    simp [hi, he] <;> ring


private theorem clifford_reverse_sign (A : Finset (Fin t)) (i : Fin t) (hi : i ∉ A) :
    (-1 : R)^A.card * fermionSign (reversePortSubset A) i.rev = fermionSign A i := by
  have hr : subsetBelow (reversePortSubset A) i.rev = (A.filter (i < ·)).card := by
    have he : (reversePortSubset A).filter (· < i.rev) = reversePortSubset (A.filter (i < ·)) := by
      ext j
      simp only [Finset.mem_filter, mem_reversePortSubset]
      rw [← Fin.rev_lt_rev]
      simp
    rw [subsetBelow, he, reversePortSubset, Finset.card_image_of_injective _ Fin.rev_injective]
  have hp : subsetBelow A i + (A.filter (i < ·)).card = A.card := by
    have he : A.filter (fun j => ¬j < i) = A.filter (i < ·) := by
      ext j
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hj, hjlt⟩
        exact ⟨hj, lt_of_le_of_ne (le_of_not_gt hjlt) (by intro h; exact hi (h ▸ hj))⟩
      · rintro ⟨hj, hlt⟩
        exact ⟨hj, not_lt_of_gt hlt⟩
    simpa only [subsetBelow, he] using Finset.card_filter_add_card_filter_not (s := A) (p := (· < i))
  rw [fermionSign, hr, ← hp, pow_add]
  have hs : (-1 : R)^(A.filter (i < ·)).card * (-1 : R)^(A.filter (i < ·)).card = 1 := by
    rw [← mul_pow]; simp
  rw [mul_assoc, hs, mul_one]
  rfl

private theorem clifford_boundary_wedge_blocks (z : CliffordVector t R)
    (A B : Finset (Fin t)) :
    boundaryWedge (cliffordBoundaryLinear z) (orderedEqualitySignature t) (blockJoin A B) =
      (∑ i : Fin t, if i ∈ A then fermionSign A i * z.1 i *
        (if A ∆ {i} = reversePortSubset B then 1 else 0) else 0) +
      (∑ j : Fin t, if j ∈ B then (-1 : R)^A.card * fermionSign B j * z.2 j.rev *
        (if A = reversePortSubset (B ∆ {j}) then 1 else 0) else 0) := by
  rw [boundaryWedge_eq_sum, Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [← mem_firstBlock, firstBlock_blockJoin, cliffordBoundaryLinear,
      Fin.addCases_left, blockJoin_flip_left, orderedEqualitySignature_blockJoin,
      fermionSign, clifford_below_left]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [← mem_secondBlock, secondBlock_blockJoin, cliffordBoundaryLinear,
      Fin.addCases_right, blockJoin_flip_right, orderedEqualitySignature_blockJoin,
      fermionSign, clifford_below_right, pow_add, mul_assoc]

/-- Exact identity-wire wedge representation, including the reversed output signs. -/
theorem signedCliffordMatrix_boundary (z : CliffordVector t R) :
    orderedMatrixSubsetSignature (signedCliffordMatrix z) =
      boundaryWedge (cliffordBoundaryLinear z) (orderedEqualitySignature t) := by
  funext S
  let A := firstBlock S
  let B := secondBlock S
  have hS : S = blockJoin A B := by
    ext i
    induction i using Fin.addCases with
    | left i => simp only [← mem_firstBlock, firstBlock_blockJoin]; rfl
    | right i => simp only [← mem_secondBlock, secondBlock_blockJoin]; rfl
  rw [hS, orderedMatrixSubsetSignature_blockJoin, signedCliffordMatrix_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, clifford_boundary_wedge_blocks]
  have hr : (∑ j : Fin t, if j ∈ B then (-1 : R)^A.card * fermionSign B j * z.2 j.rev *
      (if A = reversePortSubset (B ∆ {j}) then 1 else 0) else 0) =
      ∑ i : Fin t, if i ∉ A then fermionSign A i * z.2 i *
        (if A ∆ {i} = reversePortSubset B then 1 else 0) else 0 := by
    apply Fintype.sum_equiv Fin.revPerm
    intro j
    simp only [Fin.revPerm_apply]
    have hcond : A = reversePortSubset (B ∆ {j}) ↔ A ∆ {j.rev} = reversePortSubset B := by
      simp only [reversePortSubset_symmDiff, reversePortSubset_singleton]
      constructor
      · intro h; rw [h]; simp
      · intro h; rw [← h]; simp
    simp only [hcond]
    by_cases he : A ∆ {j.rev} = reversePortSubset B
    · have hA : A = reversePortSubset B ∆ {j.rev} := by rw [← he]; simp
      have hmem : j ∈ B ↔ j.rev ∉ A := by
        rw [hA]
        simp [Finset.mem_symmDiff]
      by_cases hj : j ∈ B
      · have hn := hmem.mp hj
        have hs : (-1 : R)^A.card * fermionSign B j = fermionSign A j.rev := by
          have hb : B = reversePortSubset (A ∆ {j.rev}) := by rw [he]; simp
          rw [hb, reversePortSubset_symmDiff, reversePortSubset_singleton]
          simp only [Fin.rev_rev, fermionSign_toggle_self]
          simpa using clifford_reverse_sign (R := R) A j.rev hn
        simp only [hj, hn, he, ite_true, mul_one, hs, not_false_eq_true]
      · have hn : ¬j.rev ∉ A := by simpa only [← hmem] using hj
        simp [hj, hn]
    · simp [he]
  rw [hr, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A <;> simp [hi]

/-- Every actual Clifford-vector action is an ordered matchgate matrix, including null vectors. -/
theorem signedCliffordMatrix_isMatchgate {K : Type*} [Field K]
    (z : CliffordVector t K) : OrderedMatchgateMatrix (signedCliffordMatrix z) := by
  rw [orderedMatchgateMatrix_iff, signedCliffordMatrix_boundary]
  apply (orderedEqualitySignature_matchgateIdentities t).boundaryWedge
  simp [orderedEqualitySignature, firstBlock, secondBlock, reversePortSubset]

end
end MatchgateWidth
