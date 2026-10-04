import MatchgateWidth.MatchgateIdentities

namespace MatchgateWidth

open scoped symmDiff

/-- Number of selected ports strictly preceding `i`. -/
def subsetBelow {s : ℕ} (S : Finset (Fin s)) (i : Fin s) : ℕ :=
  (S.filter (· < i)).card

private theorem neg_one_pow_card_symmDiff {α : Type*} [DecidableEq α]
    {R : Type*} [CommRing R] (A B : Finset α) :
    (-1 : R) ^ A.card * (-1 : R) ^ B.card = (-1 : R) ^ (A ∆ B).card := by
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hB
  have hd : Disjoint (A \ B) (B \ A) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_sdiff.mp hj).1
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd, ← hA, ← hB]
  rw [pow_add, pow_add, pow_add]
  have hc : (-1 : R) ^ (A ∩ B).card * (-1 : R) ^ (A ∩ B).card = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : R) ^ (A \ B).card * (-1 : R) ^ (B \ A).card) *
        ((-1 : R) ^ (A ∩ B).card * (-1 : R) ^ (A ∩ B).card) := by ring
    _ = _ := by rw [hc, mul_one]

/-- The signs of two subsets multiply to the sign of their symmetric difference. -/
theorem subsetBelow_sign_symmDiff {s : ℕ} {R : Type*} [CommRing R]
    (A B : Finset (Fin s)) (i : Fin s) :
    (-1 : R) ^ subsetBelow A i * (-1 : R) ^ subsetBelow B i =
      (-1 : R) ^ subsetBelow (A ∆ B) i := by
  unfold subsetBelow
  rw [neg_one_pow_card_symmDiff]
  congr 2
  ext k
  simp only [Finset.mem_symmDiff, Finset.mem_filter]
  tauto

private theorem sorted_below_get {s : ℕ} (xs : List (Fin s)) (hs : xs.SortedLT)
    (j : Fin xs.length) :
    (xs.toFinset.filter (· < xs[j])).card = j.val := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons a xs ih =>
    obtain ⟨ha, hx⟩ := List.sortedLT_cons.mp hs
    refine Fin.cases ?_ (fun k => ?_) j
    · have hf : (xs.toFinset.filter (· < a)) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro b hb
        obtain ⟨hb, hba⟩ := Finset.mem_filter.mp hb
        exact (not_lt_of_gt (ha b (List.mem_toFinset.mp hb))) hba
      simp [List.toFinset_cons, Finset.filter_insert, hf]
    · have hak : a < xs[k] := ha _ (List.getElem_mem k.isLt)
      have han : a ∉ xs.toFinset := by
        simpa using (List.nodup_cons.mp hs.nodup).1
      change ((a :: xs).toFinset.filter (· < xs[k])).card = k.val + 1
      rw [List.toFinset_cons, Finset.filter_insert, ite_eq_left hak,
        Finset.card_insert_of_notMem (fun h => han (Finset.mem_filter.mp h).1), ih hx k]

/-- A sorted port's zero-based position equals the number of smaller selected ports. -/
theorem subsetBelow_sort_get {s : ℕ} (S : Finset (Fin s))
    (j : Fin (S.sort (· ≤ ·)).length) :
    subsetBelow S (S.sort (· ≤ ·))[j] = j.val := by
  simpa [subsetBelow] using sorted_below_get (S.sort (· ≤ ·)) (Finset.sortedLT_sort S) j

/-- Reindex the alternating sum on sorted positions by the selected ports. -/
theorem sum_sort_sign {s : ℕ} {R : Type*} [CommRing R]
    (S : Finset (Fin s)) (w : Fin s → R) :
    (∑ j : Fin (S.sort (· ≤ ·)).length,
      (-1 : R) ^ j.val * w (S.sort (· ≤ ·))[j]) =
      ∑ i ∈ S, (-1 : R) ^ subsetBelow S i * w i := by
  apply Finset.sum_bij (fun j _ => (S.sort (· ≤ ·))[j])
  · intro j _
    exact (Finset.mem_sort (s := S) (· ≤ ·)).mp (List.getElem_mem j.isLt)
  · intro j _ k _ hjk
    apply Fin.ext
    exact (S.sort_nodup _).getElem_inj_iff.mp hjk
  · intro i hi
    have hi' : i ∈ S.sort (· ≤ ·) := by simpa using hi
    obtain ⟨j, hj, hji⟩ := List.getElem_of_mem hi'
    exact ⟨⟨j, hj⟩, Finset.mem_univ _, hji⟩
  · intro j _
    rw [subsetBelow_sort_get]

/-- The one-based sign convention contributes a common minus sign. -/
theorem sum_sort_sign_succ {s : ℕ} {R : Type*} [CommRing R]
    (S : Finset (Fin s)) (w : Fin s → R) :
    (∑ j : Fin (S.sort (· ≤ ·)).length,
      (-1 : R) ^ (j.val + 1) * w (S.sort (· ≤ ·))[j]) =
      -(∑ i ∈ S, (-1 : R) ^ subsetBelow S i * w i) := by
  simp only [pow_succ, mul_neg_one, neg_mul, Finset.sum_neg_distrib]
  rw [sum_sort_sign]

/-- A finite-set presentation of the exact alternating matchgate expression. -/
theorem matchgateSum_eq_neg_sum {s : ℕ} {R : Type*} [CommRing R]
    (G : SubsetSignature s R) (A B : Finset (Fin s)) :
    matchgateSum G A B ((A ∆ B).sort (· ≤ ·)) =
      -(∑ i ∈ A ∆ B, (-1 : R) ^ subsetBelow (A ∆ B) i *
        G (A ∆ {i}) * G (B ∆ {i})) := by
  unfold matchgateSum
  simpa only [mul_assoc] using sum_sort_sign_succ (A ∆ B)
    (fun i => G (A ∆ {i}) * G (B ∆ {i}))

end MatchgateWidth
