import MatchgateWidth.Pfaffian

/-!
# Isolated selected modes

General zero-row criterion used for forbidden qutrit codewords in Proposition
8.1. It is proved from the actual Pfaffian recurrence and skew-symmetry.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- A selected isolated mode makes an ordered Pfaffian zero, wherever it occurs. -/
theorem pfaffianList_eq_zero_of_isolated_mem (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = - A y x) (a : ι) (hrow : ∀ b, A a b = 0)
    (xs : List ι) (ha : a ∈ xs) : pfaffianList A xs = 0 := by
  induction xs using (measure List.length).wf.induction with
  | h xs ih =>
    cases xs with
    | nil => simp at ha
    | cons b ys =>
      by_cases hb : b = a
      · subst b
        exact pfaffianList_isolated_first A a ys (fun _ => hrow _)
      · have hay : a ∈ ys := (List.mem_cons.mp ha).resolve_left (Ne.symm hb)
        rw [pfaffianList]
        apply Finset.sum_eq_zero
        intro j _
        by_cases hj : ys[j] = a
        · rw [hj, hskew b a, hrow b]
          simp
        · have ham : a ∈ ys.eraseIdx j.val := by
            obtain ⟨i, hi, he⟩ := List.getElem_of_mem hay
            apply List.mem_eraseIdx_iff_getElem.mpr
            refine ⟨i, hi, ?_, he⟩
            intro hij
            subst i
            exact hj he
          have hlt : (ys.eraseIdx j.val).length < (b :: ys).length := by
            have := List.length_eraseIdx_le ys j.val
            simp only [List.length_cons]
            omega
          rw [ih _ hlt ham]
          simp

end MatchgateWidth
