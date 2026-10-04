import MatchgateWidth.MatchgateIdentities
import MatchgateWidth.PfaffianInsertion
import MatchgateWidth.SubsetSignParity

/-!
# Principal Pfaffians satisfy the literal matchgate identities

The starting bilinear identity is a direct double use of the ordered recursive
expansion. All its terms cancel by skew symmetry; it does not assume any
matchgate identity or graphical realization.
-/

namespace MatchgateWidth

open scoped symmDiff

variable {R ι : Type*} [CommRing R]

/-- The ordered bilinear Pfaffian deletion identity. The two double sums cancel
term by term by skew symmetry, before any sorted-set bookkeeping is used. -/
theorem pfaffianList_bilinear_deletion (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (xs ys : List ι) :
    (∑ j : Fin xs.length, (-1 : R) ^ j.val *
      pfaffianList A (xs.eraseIdx j.val) * pfaffianList A (xs[j] :: ys)) +
    (∑ j : Fin ys.length, (-1 : R) ^ j.val *
      pfaffianList A (ys.eraseIdx j.val) * pfaffianList A (ys[j] :: xs)) = 0 := by
  simp only [pfaffianList_cons_signedEraseSum]
  simp only [← pfaffianList_cons_signedEraseSum, pfaffianList.eq_2,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [hskew xs[i] ys[j]]
  ring

/-- Deleting a position from an increasing boundary list gives exactly the
increasing list of the subset with that element removed. -/
theorem sort_erase_getElem {s : ℕ} (S : Finset (Fin s))
    (j : Fin (S.sort (· ≤ ·)).length) :
    (S.erase (S.sort (· ≤ ·))[j]).sort (· ≤ ·) =
      (S.sort (· ≤ ·)).eraseIdx j.val := by
  have hn := Finset.sort_nodup S (· ≤ ·)
  have hset : ((S.sort (· ≤ ·)).eraseIdx j.val).toFinset =
      S.erase (S.sort (· ≤ ·))[j] := by
    rw [← hn.erase_getElem j.val j.isLt]
    ext i
    simp only [List.mem_toFinset, hn.mem_erase_iff, Finset.mem_erase,
      Finset.mem_sort, Fin.getElem_fin]
  have hs : ((S.sort (· ≤ ·)).eraseIdx j.val).SortedLT :=
    ((Finset.sortedLT_sort S).pairwise.sublist (List.eraseIdx_sublist _ _)).sortedLT
  rw [← hset]
  exact (List.toFinset_sort (· ≤ ·) hs.nodup).mpr hs.sortedLE.pairwise

/-- The increasing-order principal Pfaffian coordinate of a finite subset. -/
def principalPfaffian {s : ℕ} (A : Matrix (Fin s) (Fin s) R) :
    SubsetSignature s R := fun S => pfaffianList A (S.sort (· ≤ ·))

/-- The bilinear identity reindexed by finite subsets. -/
theorem principalPfaffian_bilinear_deletion {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (hskew : ∀ x y, A x y = -A y x)
    (S T : Finset (Fin s)) :
    (∑ i ∈ S, (-1 : R) ^ subsetBelow S i * principalPfaffian A (S.erase i) *
      pfaffianList A (i :: T.sort (· ≤ ·))) +
    (∑ i ∈ T, (-1 : R) ^ subsetBelow T i * principalPfaffian A (T.erase i) *
      pfaffianList A (i :: S.sort (· ≤ ·))) = 0 := by
  have h := pfaffianList_bilinear_deletion A hskew (S.sort (· ≤ ·)) (T.sort (· ≤ ·))
  simp_rw [← sort_erase_getElem] at h
  simp only [mul_assoc] at h ⊢
  rw [sum_sort_sign S (fun i => pfaffianList A ((S.erase i).sort (· ≤ ·)) *
    pfaffianList A (i :: T.sort (· ≤ ·))),
    sum_sort_sign T (fun i => pfaffianList A ((T.erase i).sort (· ≤ ·)) *
    pfaffianList A (i :: S.sort (· ≤ ·)))] at h
  exact h

private theorem symmDiff_singleton_of_mem {s : ℕ}
    (S : Finset (Fin s)) (i : Fin s) (hi : i ∈ S) :
    S ∆ {i} = S.erase i := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
  grind

private theorem symmDiff_singleton_of_not_mem {s : ℕ}
    (S : Finset (Fin s)) (i : Fin s) (hi : i ∉ S) :
    S ∆ {i} = insert i S := by
  ext j
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  grind

/-- One side of the bilinear identity is the contribution from the corresponding
half of the symmetric difference. Terms in the intersection vanish. -/
theorem principalPfaffian_deletion_half {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (hskew : ∀ x y, A x y = -A y x)
    (hdiag : ∀ x, A x x = 0)
    (S T : Finset (Fin s)) :
    (∑ i ∈ S, (-1 : R) ^ subsetBelow S i * principalPfaffian A (S.erase i) *
      pfaffianList A (i :: T.sort (· ≤ ·))) =
    ∑ i ∈ S \ T, (-1 : R) ^ subsetBelow (S ∆ T) i *
      principalPfaffian A (S ∆ {i}) * principalPfaffian A (T ∆ {i}) := by
  calc
    _ = ∑ i ∈ S \ T, (-1 : R) ^ subsetBelow S i *
        principalPfaffian A (S.erase i) * pfaffianList A (i :: T.sort (· ≤ ·)) := by
      symm
      apply Finset.sum_subset Finset.sdiff_subset
      intro i hi hn
      have hit : i ∈ T := by simpa [Finset.mem_sdiff, hi] using hn
      rw [pfaffianList_mem_sort_eq_zero_of_diag_zero A hskew hdiag T i hit, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨hiS, hiT⟩ := Finset.mem_sdiff.mp hi
      rw [symmDiff_singleton_of_mem S i hiS, symmDiff_singleton_of_not_mem T i hiT,
        pfaffianList_insert_sort A hskew T i hiT]
      change (-1 : R) ^ subsetBelow S i * principalPfaffian A (S.erase i) *
          ((-1 : R) ^ subsetBelow T i * principalPfaffian A (insert i T)) = _
      rw [← subsetBelow_sign_symmDiff]
      ring

/-- Principal Pfaffian coordinates satisfy every literal, increasing-symmetric-
difference matchgate identity. This direction is proved independently of the
converse reconstruction theorem. -/
theorem principalPfaffian_matchgateIdentities {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (hskew : ∀ x y, A x y = -A y x)
    (hdiag : ∀ x, A x x = 0) :
    MatchgateIdentities (principalPfaffian A) := by
  intro S T
  rw [matchgateSum_eq_neg_sum]
  have h := principalPfaffian_bilinear_deletion A hskew S T
  rw [principalPfaffian_deletion_half A hskew hdiag S T,
    principalPfaffian_deletion_half A hskew hdiag T S, symmDiff_comm T S] at h
  have hd : Disjoint (S \ T) (T \ S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  have hsum : (∑ i ∈ S ∆ T, (-1 : R) ^ subsetBelow (S ∆ T) i *
      principalPfaffian A (S ∆ {i}) * principalPfaffian A (T ∆ {i})) = 0 := by
    change (∑ i ∈ (S \ T) ∪ (T \ S), (-1 : R) ^ subsetBelow (S ∆ T) i *
      principalPfaffian A (S ∆ {i}) * principalPfaffian A (T ∆ {i})) = 0
    rw [Finset.sum_union hd]
    convert h using 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum, neg_zero]

/-- Multiplying every coordinate by one scalar preserves the quadratic identities. -/
theorem MatchgateIdentities.const_mul {s : ℕ} {G : SubsetSignature s R}
    (hG : MatchgateIdentities G) (c : R) :
    MatchgateIdentities (fun S => c * G S) := by
  intro S T
  have hscale : matchgateSum (fun U => c * G U) S T ((S ∆ T).sort (· ≤ ·)) =
      (c * c) * matchgateSum G S T ((S ∆ T).sort (· ≤ ·)) := by
    unfold matchgateSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hscale, hG S T, mul_zero]

/-- Every actual principal-Pfaffian chart satisfies the Boolean matchgate
identities, over every commutative ring and including zero scale. -/
theorem pfaffianChart_booleanMatchgateIdentities {s : ℕ}
    (a : PfaffianChartParameter s → R) : BooleanMatchgateIdentities (pfaffianChart a) := by
  have h := (principalPfaffian_matchgateIdentities (pfaffianChartMatrix a)
    (fun x y => pfaffianChartMatrix_skew a y x) (pfaffianChartMatrix_diag a)).const_mul (a none)
  have heq : (fun S => pfaffianChart a ((booleanSubsetEquiv s).symm S)) =
      (fun S => a none * principalPfaffian (pfaffianChartMatrix a) S) := by
    funext S
    unfold pfaffianChart pfaffianSelectedPorts principalPfaffian
    congr 2
    have he := (booleanSubsetEquiv s).apply_symm_apply S
    exact congrArg (fun T : Finset (Fin s) => T.sort (· ≤ ·)) he
  unfold BooleanMatchgateIdentities
  rw [heq]
  exact h

/-- Common XOR pivoting preserves the literal Boolean identities. -/
theorem BooleanMatchgateIdentities.pivot {s : ℕ} {f : BooleanTable s R}
    (hf : BooleanMatchgateIdentities f) (pivot : BooleanInput s) :
    BooleanMatchgateIdentities (fun z => f (pfaffianXor pivot z)) := by
  have h := hf.subsetPivot (booleanSubsetEquiv s pivot)
  have heq : (fun S => f (pfaffianXor pivot ((booleanSubsetEquiv s).symm S))) =
      subsetPivot (fun S => f ((booleanSubsetEquiv s).symm S)) (booleanSubsetEquiv s pivot) := by
    funext S
    unfold subsetPivot
    congr 1
    apply (booleanSubsetEquiv s).injective
    simp only [booleanSubsetEquiv_xor, Equiv.apply_symm_apply, symmDiff_comm]
  unfold BooleanMatchgateIdentities
  rw [heq]
  exact h

/-- All zero-sign XOR pivot charts satisfy the Boolean identities. Arbitrary
independently chosen coordinate signs are not asserted to preserve them. -/
theorem pfaffianPivotChart_booleanMatchgateIdentities {s : ℕ}
    (pivot : BooleanInput s) (a : PfaffianChartParameter s → R) :
    BooleanMatchgateIdentities (pfaffianPivotChart pivot (fun _ => 0) a) := by
  have heq : pfaffianPivotChart pivot (fun _ => 0) a =
      (fun z => pfaffianChart a (pfaffianXor pivot z)) := by
    funext z
    simp [pfaffianPivotChart]
  rw [heq]
  exact (pfaffianChart_booleanMatchgateIdentities a).pivot pivot

/-- Over a field, the literal matchgate locus is exactly the union of its
principal-Pfaffian XOR charts. The converse uses the independently proved
Pfaffian deletion identity above. -/
theorem booleanMatchgateIdentities_iff_exists_pfaffianPivotChart
    {s : ℕ} {K : Type*} [Field K] (f : BooleanTable s K) :
    BooleanMatchgateIdentities f ↔
      ∃ (pivot : BooleanInput s) (a : PfaffianChartParameter s → K),
        f = pfaffianPivotChart pivot (fun _ => 0) a := by
  constructor
  · exact BooleanMatchgateIdentities.exists_pfaffianPivotChart
  · rintro ⟨pivot, a, rfl⟩
    exact pfaffianPivotChart_booleanMatchgateIdentities pivot a

end MatchgateWidth
