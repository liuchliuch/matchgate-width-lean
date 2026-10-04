import MatchgateWidth.Pfaffian

/-!
# Ordered Pfaffian block products

The recursive ordered Pfaffian factors over consecutive blocks when the entries
from an earlier block to a later block vanish. Neither skew-symmetry nor an
even-length assumption is needed for this purely algebraic identity.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- The ordered Pfaffian depends only on matrix entries indexed by its list. -/
theorem pfaffianList_congr (A B : Matrix ι ι R) (xs : List ι)
    (hAB : ∀ x ∈ xs, ∀ y ∈ xs, A x y = B x y) :
    pfaffianList A xs = pfaffianList B xs := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [pfaffianList, pfaffianList]
      apply Finset.sum_congr rfl
      intro j _
      rw [hAB a (by simp) xs[j] (List.mem_cons_of_mem a (List.getElem_mem j.isLt))]
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        have := List.length_eraseIdx_le xs j.val
        simp only [List.length_cons]
        omega
      rw [ih (xs.eraseIdx j.val) hlt]
      intro x hx y hy
      exact hAB x (List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hx))
        y (List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hy))

/-- Relabeling the ordered list is equivalent to pulling back both matrix indices.
The map need not be injective, since this is an identity of the recursion. -/
theorem pfaffianList_map {κ : Type*} (A : Matrix κ κ R) (f : ι → κ) (xs : List ι) :
    pfaffianList A (xs.map f) = pfaffianList (fun x y => A (f x) (f y)) xs := by
  let B : Matrix ι ι R := fun x y => A (f x) (f y)
  change pfaffianList A (xs.map f) = pfaffianList B xs
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [List.map_cons, pfaffianList, pfaffianList]
      let g : Fin (xs.map f).length → R := fun j =>
        (-1 : R) ^ j.val * A (f a) (xs.map f)[j] *
          pfaffianList A ((xs.map f).eraseIdx j.val)
      change (∑ j, g j) = _
      rw [← Fin.sum_congr' g (List.length_map f).symm]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [g]
      rw [List.getElem_map, List.eraseIdx_map]
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        have := List.length_eraseIdx_le xs j.val
        simp only [List.length_cons]
        omega
      rw [ih (xs.eraseIdx j.val) hlt]

/-- Applying a ring homomorphism entrywise commutes with the ordered Pfaffian.
In particular, this allows exact evaluation of polynomial-valued matrices. -/
theorem pfaffianList_map_ringHom {S : Type*} [CommRing S]
    (f : R →+* S) (A : Matrix ι ι R) (xs : List ι) :
    pfaffianList (fun i j => f (A i j)) xs = f (pfaffianList A xs) := by
  let B : Matrix ι ι S := fun i j => f (A i j)
  change pfaffianList B xs = f (pfaffianList A xs)
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [pfaffianList, pfaffianList, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        have := List.length_eraseIdx_le xs j.val
        simp only [List.length_cons]
        omega
      rw [ih (xs.eraseIdx j.val) hlt]
      simp only [B, map_mul, map_pow, map_neg, map_one]

/-- Consecutive blocks with zero upper-cross entries have multiplicative
ordered Pfaffians. The identity also includes odd-sized and empty blocks. -/
theorem pfaffianList_append (A : Matrix ι ι R) (xs ys : List ι)
    (hcross : ∀ x ∈ xs, ∀ y ∈ ys, A x y = 0) :
    pfaffianList A (xs ++ ys) = pfaffianList A xs * pfaffianList A ys := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      rw [List.cons_append, pfaffianList]
      let f : Fin (xs ++ ys).length → R := fun j =>
        (-1 : R) ^ j.val * A a (xs ++ ys)[j] *
          pfaffianList A ((xs ++ ys).eraseIdx j.val)
      change (∑ j, f j) = _
      rw [← Fin.sum_congr' f (List.length_append (as := xs) (bs := ys)).symm, Fin.sum_univ_add]
      have hright :
          (∑ j : Fin ys.length,
            f ((Fin.natAdd xs.length j).cast (List.length_append (as := xs) (bs := ys)).symm)) = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        dsimp [f]
        rw [List.getElem_append_right (by omega)]
        have hj : A a ys[j.val] = 0 :=
          hcross a (by simp) ys[j.val] (List.getElem_mem j.isLt)
        simp only [Nat.add_sub_cancel_left, hj, mul_zero, zero_mul]
      rw [hright, add_zero]
      rw [pfaffianList, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f]
      rw [List.getElem_append_left j.isLt,
        List.eraseIdx_append_of_lt_length j.isLt]
      have hlt : (xs.eraseIdx j.val).length < (a :: xs).length := by
        have := List.length_eraseIdx_le xs j.val
        simp only [List.length_cons]
        omega
      rw [ih (xs.eraseIdx j.val) hlt]
      · simp only [mul_assoc]
      · intro x hx y hy
        exact hcross x (List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hx)) y hy

end MatchgateWidth
