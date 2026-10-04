import MatchgateWidth.GaussianCross
import MatchgateWidth.PfaffianInsertion

/-!
# Normalization of arbitrary input-coordinate lists

Permuting input coordinates changes the Pfaffian by a scalar independent of all
output coordinates. Repeated input coordinates give the zero row. Thus every
input list is proportional to the canonical finite-subset row, while the output
list and its order remain arbitrary.
-/

namespace MatchgateWidth

variable {R ι I J : Type*} [CommRing R]

/-- A permutation of an interior coordinate list acts by one scalar, uniformly
for every fixed prefix and suffix. -/
theorem pfaffianList_perm_exists_scalar (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x)
    {xs ys : List ι} (hperm : xs.Perm ys) :
    ∃ c : R, ∀ pre suf : List ι,
      pfaffianList A (pre ++ xs ++ suf) =
        c * pfaffianList A (pre ++ ys ++ suf) := by
  induction hperm with
  | nil => exact ⟨1, fun pre suf => by simp⟩
  | @cons a xs ys hp ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c, fun pre suf => ?_⟩
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      hc (pre ++ [a]) suf
  | swap a b xs =>
    refine ⟨-1, fun pre suf => ?_⟩
    simpa only [List.append_assoc, List.cons_append, neg_one_mul] using
      pfaffianList_swap_adjacent A hskew b a pre (xs ++ suf)
  | trans hp hq ih₁ ih₂ =>
    obtain ⟨c, hc⟩ := ih₁
    obtain ⟨d, hd⟩ := ih₂
    refine ⟨c * d, fun pre suf => ?_⟩
    rw [hc, hd, mul_assoc]

/-- A repeated coordinate anywhere in an interior list makes every such
Pfaffian vanish, regardless of the surrounding coordinates. -/
theorem pfaffianList_not_nodup_eq_zero [NoZeroDivisors R] [CharZero R]
    (A : Matrix ι ι R) (hskew : ∀ x y, A x y = -A y x)
    (xs : List ι) (hxs : ¬xs.Nodup) (pre suf : List ι) :
    pfaffianList A (pre ++ xs ++ suf) = 0 := by
  classical
  induction xs generalizing pre with
  | nil => exact (hxs List.nodup_nil).elim
  | cons a xs ih =>
    by_cases ha : a ∈ xs
    · obtain ⟨middle, tail, rfl⟩ := List.append_of_mem ha
      have h := pfaffianList_move_right A hskew a middle pre (a :: (tail ++ suf))
      rw [pfaffianList_adjacent_duplicate A hskew a (pre ++ middle) (tail ++ suf),
        mul_zero] at h
      simpa only [List.append_assoc, List.cons_append] using h
    · have hn : ¬xs.Nodup := fun hn => hxs (hn.cons ha)
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        ih hn (pre ++ [a])

/-- The order-embedding enumeration used by Gaussian signatures is the sorted
list of the finite set. -/
theorem gaussianSubsetList_eq_sort [LinearOrder I] (s : Finset I) :
    gaussianSubsetList s = s.sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [gaussianSubsetList, List.getElem_ofFn,
      Set.powersetCard.ofFinEmbEquiv_symm_apply]
    exact Finset.orderEmbOfFin_apply s rfl _

/-- Normalizing the input list to its increasing finite subset changes a skew
Pfaffian row by one scalar independent of the supplied output list and order. -/
theorem pfaffianList_input_normalization [NoZeroDivisors R] [CharZero R]
    [LinearOrder I] (A : Matrix (I ⊕ J) (I ⊕ J) R)
    (hskew : ∀ x y, A x y = -A y x) (xs : List I) :
    ∃ c : R, ∀ ys : List J,
      pfaffianList A (xs.map Sum.inl ++ ys.map Sum.inr) =
        c * pfaffianList A
          ((gaussianSubsetList xs.toFinset).map Sum.inl ++ ys.map Sum.inr) := by
  classical
  by_cases hn : xs.Nodup
  · have hp : xs.Perm (gaussianSubsetList xs.toFinset) := by
      rw [gaussianSubsetList_eq_sort]
      exact (List.toFinset_toList hn).symm.trans
        (Finset.sort_perm_toList xs.toFinset (· ≤ ·)).symm
    obtain ⟨c, hc⟩ := pfaffianList_perm_exists_scalar A hskew (hp.map Sum.inl)
    refine ⟨c, fun ys => ?_⟩
    simpa only [List.nil_append] using hc [] (ys.map Sum.inr)
  · refine ⟨0, fun ys => ?_⟩
    rw [zero_mul]
    have hm : ¬(xs.map (Sum.inl : I → I ⊕ J)).Nodup := by
      intro hm
      exact hn (List.Nodup.of_map Sum.inl hm)
    simpa only [List.nil_append] using
      pfaffianList_not_nodup_eq_zero A hskew (xs.map Sum.inl) hm [] (ys.map Sum.inr)

end MatchgateWidth
