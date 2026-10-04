import MatchgateWidth.PfaffianPermutation
import Mathlib.Data.Finset.Sort

/-!
# Insertion signs and repeated coordinates for Pfaffians

These lemmas identify the sign between a first-coordinate Pfaffian expansion
and a principal Pfaffian indexed by an increasing finite set.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- Moving a coordinate through a list contributes one minus sign per entry. -/
theorem pfaffianList_move_right (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a : ι) (middle pre suf : List ι) :
    pfaffianList A (pre ++ a :: (middle ++ suf)) =
      (-1 : R) ^ middle.length * pfaffianList A (pre ++ middle ++ a :: suf) := by
  induction middle generalizing pre with
  | nil => simp
  | cons b middle ih =>
    rw [List.cons_append]
    rw [pfaffianList_swap_adjacent A hskew a b pre (middle ++ suf)]
    have h := ih (pre ++ [b])
    simp only [List.append_assoc, List.cons_append, List.nil_append] at h
    rw [h]
    simp only [List.length_cons, pow_succ, List.cons_append, List.append_assoc]
    ring

/-- A repeated adjacent coordinate makes the Pfaffian vanish in characteristic
zero, without any distinctness assumptions on the remaining coordinates. -/
theorem pfaffianList_adjacent_duplicate [NoZeroDivisors R] [CharZero R]
    (A : Matrix ι ι R) (hskew : ∀ x y, A x y = -A y x)
    (a : ι) (pre suf : List ι) :
    pfaffianList A (pre ++ a :: a :: suf) = 0 := by
  have h := pfaffianList_swap_adjacent A hskew a a pre suf
  have htwo : (2 : R) * pfaffianList A (pre ++ a :: a :: suf) = 0 := by
    calc
      _ = pfaffianList A (pre ++ a :: a :: suf) +
          pfaffianList A (pre ++ a :: a :: suf) := by ring
      _ = 0 := eq_neg_iff_add_eq_zero.mp h
  exact (mul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- If the head coordinate already occurs in the tail, the Pfaffian vanishes. -/
theorem pfaffianList_head_duplicate [NoZeroDivisors R] [CharZero R]
    (A : Matrix ι ι R) (hskew : ∀ x y, A x y = -A y x)
    {a : ι} {xs : List ι} (ha : a ∈ xs) :
    pfaffianList A (a :: xs) = 0 := by
  obtain ⟨pre, suf, rfl⟩ := List.append_of_mem ha
  have h := pfaffianList_move_right A hskew a pre [] (a :: suf)
  simpa only [List.nil_append, pfaffianList_adjacent_duplicate A hskew,
    mul_zero] using h

private theorem signedEraseSum_sub_insertion (f : ι → R) (F G : List ι → R)
    (xs : List ι) :
    signedEraseSum f (fun ys => F ys - G ys) xs =
      signedEraseSum f F xs - signedEraseSum f G xs := by
  induction xs generalizing F G with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [ih]
    ring

private theorem signedEraseSum_smul_insertion (f : ι → R) (F : List ι → R)
    (c : R) (xs : List ι) :
    signedEraseSum f (fun ys => c * F ys) xs = c * signedEraseSum f F xs := by
  induction xs generalizing F with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [ih]
    ring

/-- A signed deletion operator squares to zero over every commutative ring. -/
theorem signedEraseSum_square_zero (f : ι → R) (F : List ι → R) (xs : List ι) :
    signedEraseSum f (signedEraseSum f F) xs = 0 := by
  induction xs generalizing F with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [signedEraseSum_sub_insertion, signedEraseSum_smul_insertion, ih]
    ring

/-- Two equal initial coordinates vanish over any ring when the matrix diagonal
vanishes. This also handles characteristic two. -/
theorem pfaffianList_head_pair_of_diag_zero (A : Matrix ι ι R)
    (hdiag : ∀ x, A x x = 0) (a : ι) (xs : List ι) :
    pfaffianList A (a :: a :: xs) = 0 := by
  simp only [pfaffianList_cons_signedEraseSum, signedEraseSum, hdiag, zero_mul]
  rw [signedEraseSum_square_zero]
  simp

/-- The characteristic-free repeated-head law for an alternating matrix. -/
theorem pfaffianList_head_duplicate_of_diag_zero (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (hdiag : ∀ x, A x x = 0)
    {a : ι} {xs : List ι} (ha : a ∈ xs) :
    pfaffianList A (a :: xs) = 0 := by
  obtain ⟨pre, suf, rfl⟩ := List.append_of_mem ha
  have h := pfaffianList_move_right A hskew a pre [a] suf
  simp only [List.cons_append, List.nil_append,
    pfaffianList_head_pair_of_diag_zero A hdiag] at h
  exact neg_one_pow_mul_eq_zero_iff.mp h.symm

/-- Equal adjacent coordinates vanish in every characteristic for an alternating
matrix, even after an arbitrary prefix. -/
theorem pfaffianList_adjacent_duplicate_of_diag_zero (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (hdiag : ∀ x, A x x = 0)
    (a : ι) (pre suf : List ι) :
    pfaffianList A (pre ++ a :: a :: suf) = 0 := by
  have h := pfaffianList_move_right A hskew a pre [] (a :: suf)
  simp only [List.nil_append] at h
  have hz : pfaffianList A (a :: (pre ++ a :: suf)) = 0 :=
    pfaffianList_head_duplicate_of_diag_zero A hskew hdiag (by simp)
  rw [hz] at h
  exact neg_one_pow_mul_eq_zero_iff.mp h.symm

section Ordered

variable [LinearOrder ι]

/-- Inserting a head coordinate into a sorted list has the sign prescribed by
the number of coordinates strictly below it. The prefix is arbitrary. -/
theorem pfaffianList_orderedInsert (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a : ι)
    (xs : List ι) (hs : xs.Pairwise (· ≤ ·)) (pre : List ι) :
    pfaffianList A (pre ++ a :: xs) =
      (-1 : R) ^ (xs.filter (fun x => decide (x < a))).length *
        pfaffianList A (pre ++ xs.orderedInsert (· ≤ ·) a) := by
  induction xs generalizing pre with
  | nil => simp
  | cons b xs ih =>
    obtain ⟨hb, hs⟩ := List.pairwise_cons.mp hs
    by_cases hab : a ≤ b
    · have hfilter : xs.filter (fun x => decide (x < a)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simp only [decide_eq_true_eq]
        exact not_lt_of_ge (hab.trans (hb x hx))
      simp [List.orderedInsert_cons_of_le _ _ hab, hfilter, not_lt_of_ge hab]
    · have hba : b < a := lt_of_not_ge hab
      rw [List.orderedInsert_of_not_le _ _ hab]
      rw [pfaffianList_swap_adjacent A hskew a b pre xs]
      have h := ih hs (pre ++ [b])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h
      rw [h]
      simp only [List.filter_cons, decide_eq_true hba, ite_true, List.length_cons,
        pow_succ]
      ring

private theorem sort_insert_eq_orderedInsert (S : Finset ι) (a : ι) (ha : a ∉ S) :
    (insert a S).sort (· ≤ ·) = (S.sort (· ≤ ·)).orderedInsert (· ≤ ·) a := by
  let xs := S.sort (· ≤ ·)
  have hp := List.perm_orderedInsert (· ≤ ·) a xs
  have hn : (xs.orderedInsert (· ≤ ·) a).Nodup := by
    apply hp.symm.nodup
    simp [xs, ha]
  have ht : (xs.orderedInsert (· ≤ ·) a).toFinset = insert a S := by
    ext x
    simp [List.mem_orderedInsert, xs]
  rw [← ht]
  exact (List.toFinset_sort (· ≤ ·) hn).mpr
    (List.Pairwise.orderedInsert a xs (Finset.pairwise_sort S (· ≤ ·)))

/-- The head-insertion sign for an increasing principal-Pfaffian index set. -/
theorem pfaffianList_insert_sort (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (S : Finset ι) (a : ι) (ha : a ∉ S) :
    pfaffianList A (a :: S.sort (· ≤ ·)) =
      (-1 : R) ^ (S.filter (· < a)).card *
        pfaffianList A ((insert a S).sort (· ≤ ·)) := by
  have hlength : ((S.sort (· ≤ ·)).filter (fun x => decide (x < a))).length =
      (S.filter (· < a)).card := by
    rw [← List.toFinset_card_of_nodup
      (List.Nodup.filter _ (Finset.sort_nodup S (· ≤ ·)))]
    simp [List.toFinset_filter]
  rw [sort_insert_eq_orderedInsert S a ha, ← hlength]
  simpa only [List.nil_append] using
    pfaffianList_orderedInsert A hskew a (S.sort (· ≤ ·))
      (Finset.pairwise_sort S (· ≤ ·)) []

/-- A repeated head coordinate vanishes for a finite-set principal Pfaffian. -/
theorem pfaffianList_mem_sort_eq_zero [NoZeroDivisors R] [CharZero R]
    (A : Matrix ι ι R) (hskew : ∀ x y, A x y = -A y x)
    (S : Finset ι) (a : ι) (ha : a ∈ S) :
    pfaffianList A (a :: S.sort (· ≤ ·)) = 0 := by
  apply pfaffianList_head_duplicate A hskew
  simpa using ha

/-- The finite-set repeated-head law over any commutative ring. -/
theorem pfaffianList_mem_sort_eq_zero_of_diag_zero
    (A : Matrix ι ι R) (hskew : ∀ x y, A x y = -A y x)
    (hdiag : ∀ x, A x x = 0) (S : Finset ι) (a : ι) (ha : a ∈ S) :
    pfaffianList A (a :: S.sort (· ≤ ·)) = 0 := by
  apply pfaffianList_head_duplicate_of_diag_zero A hskew hdiag
  simpa using ha

end Ordered
end MatchgateWidth
