import MatchgateWidth.PfaffianBlocks

/-!
# Order and sign of the recursive Pfaffian

Signed deletion operators anticommute. This gives the alternating law for the
ordered Pfaffian directly from its recursion, including matrices with arbitrary
cross-couplings. Consequently, permuting consecutive two-coordinate chunks does
not change the Pfaffian.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- Signed sum over deletion of one list entry. -/
def signedEraseSum (f : ι → R) (F : List ι → R) : List ι → R
  | [] => 0
  | x :: xs => f x * F xs - signedEraseSum f (fun ys => F (x :: ys)) xs

private theorem signedEraseSum_sub (f : ι → R) (F G : List ι → R) (xs : List ι) :
    signedEraseSum f (fun ys => F ys - G ys) xs =
      signedEraseSum f F xs - signedEraseSum f G xs := by
  induction xs generalizing F G with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [ih]
    ring

private theorem signedEraseSum_smul (f : ι → R) (F : List ι → R) (c : R)
    (xs : List ι) :
    signedEraseSum f (fun ys => c * F ys) xs = c * signedEraseSum f F xs := by
  induction xs generalizing F with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [ih]
    ring

private theorem signedEraseSum_neg (f : ι → R) (F : List ι → R) (xs : List ι) :
    signedEraseSum f (fun ys => -F ys) xs = -signedEraseSum f F xs := by
  simpa only [neg_one_mul] using signedEraseSum_smul f F (-1) xs

/-- Signed single-entry deletion operators anticommute, over any commutative ring. -/
theorem signedEraseSum_anticommute (f g : ι → R) (F : List ι → R) (xs : List ι) :
    signedEraseSum f (signedEraseSum g F) xs =
      -signedEraseSum g (signedEraseSum f F) xs := by
  induction xs generalizing F with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [signedEraseSum_sub, signedEraseSum_sub,
      signedEraseSum_smul, signedEraseSum_smul, ih]
    ring

private theorem signedEraseSum_eq_sum (f : ι → R) (F : List ι → R) (xs : List ι) :
    signedEraseSum f F xs =
      ∑ j : Fin xs.length, (-1 : R) ^ j.val * f xs[j] * F (xs.eraseIdx j.val) := by
  induction xs generalizing F with
  | nil => simp [signedEraseSum]
  | cons x xs ih =>
    simp only [signedEraseSum, List.length_cons, Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul,
      List.eraseIdx_zero, Fin.val_succ, List.eraseIdx_cons_succ]
    rw [ih, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [pow_succ, Fin.getElem_fin, Fin.val_succ, List.getElem_cons_succ]
    ring

/-- The ordered Pfaffian is a signed deletion sum along its first coordinate. -/
theorem pfaffianList_cons_signedEraseSum (A : Matrix ι ι R) (a : ι) (xs : List ι) :
    pfaffianList A (a :: xs) = signedEraseSum (A a) (pfaffianList A) xs := by
  rw [pfaffianList, signedEraseSum_eq_sum]

/-- Swapping the first two coordinates negates a skew matrix's ordered Pfaffian.
No assumption on the parity, distinctness, characteristic, or diagonal is needed. -/
theorem pfaffianList_swap_head (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a b : ι) (xs : List ι) :
    pfaffianList A (a :: b :: xs) = -pfaffianList A (b :: a :: xs) := by
  simp only [pfaffianList_cons_signedEraseSum, signedEraseSum]
  rw [signedEraseSum_anticommute, hskew a b]
  ring

private theorem signedEraseSum_congr_length (f : ι → R) (F G : List ι → R)
    (xs : List ι) (h : ∀ ys, ys.length < xs.length → F ys = G ys) :
    signedEraseSum f F xs = signedEraseSum f G xs := by
  induction xs generalizing F G with
  | nil => rfl
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [h xs (by simp), ih]
    intro ys hy
    exact h (x :: ys) (by simp only [List.length_cons]; omega)

private theorem signedEraseSum_swap (f : ι → R) (F : List ι → R)
    (a b : ι) (pre suf : List ι)
    (h : ∀ pre' suf' : List ι, pre'.length + suf'.length < pre.length + suf.length →
      F (pre' ++ a :: b :: suf') = -F (pre' ++ b :: a :: suf')) :
    signedEraseSum f F (pre ++ a :: b :: suf) =
      -signedEraseSum f F (pre ++ b :: a :: suf) := by
  induction pre generalizing F with
  | nil =>
    simp only [List.nil_append, signedEraseSum]
    have heq : signedEraseSum f (fun ys => F (a :: b :: ys)) suf =
        -signedEraseSum f (fun ys => F (b :: a :: ys)) suf := by
      rw [← signedEraseSum_neg]
      apply signedEraseSum_congr_length
      intro ys hy
      exact h [] ys (by simpa using hy)
    rw [heq]
    ring
  | cons x pre ih =>
    simp only [List.cons_append, signedEraseSum]
    rw [h pre suf (by simp only [List.length_cons]; omega)]
    rw [ih]
    · ring
    · intro pre' suf' hlt
      exact h (x :: pre') suf' (by simp only [List.length_cons]; omega)

/-- Swapping any adjacent coordinates negates a skew matrix's ordered Pfaffian. -/
theorem pfaffianList_swap_adjacent (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a b : ι) (pre suf : List ι) :
    pfaffianList A (pre ++ a :: b :: suf) =
      -pfaffianList A (pre ++ b :: a :: suf) := by
  generalize hn : pre.length + suf.length = n
  induction n using Nat.strong_induction_on generalizing pre suf with
  | h n ih =>
    cases pre with
    | nil => exact pfaffianList_swap_head A hskew a b suf
    | cons x pre =>
      simp only [List.cons_append, pfaffianList_cons_signedEraseSum]
      apply signedEraseSum_swap
      intro pre' suf' hlt
      apply ih (pre'.length + suf'.length) _ pre' suf' rfl
      simp only [List.length_cons] at hn
      omega

/-- Interchanging adjacent two-coordinate chunks preserves the ordered Pfaffian.
All four intervening coordinate transpositions have their signs accounted for. -/
theorem pfaffianList_swap_pairChunks (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (a b c d : ι) (pre suf : List ι) :
    pfaffianList A (pre ++ a :: b :: c :: d :: suf) =
      pfaffianList A (pre ++ c :: d :: a :: b :: suf) := by
  calc
    _ = -pfaffianList A (pre ++ a :: c :: b :: d :: suf) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        pfaffianList_swap_adjacent A hskew b c (pre ++ [a]) (d :: suf)
    _ = pfaffianList A (pre ++ c :: a :: b :: d :: suf) := by
      rw [pfaffianList_swap_adjacent A hskew a c pre (b :: d :: suf), neg_neg]
    _ = -pfaffianList A (pre ++ c :: a :: d :: b :: suf) := by
      simpa only [List.append_assoc, List.cons_append, List.nil_append] using
        pfaffianList_swap_adjacent A hskew b d (pre ++ [c, a]) suf
    _ = pfaffianList A (pre ++ c :: d :: a :: b :: suf) := by
      have h := pfaffianList_swap_adjacent A hskew a d (pre ++ [c]) (b :: suf)
      simp only [List.append_assoc, List.cons_append, List.nil_append] at h
      rw [h, neg_neg]

/-- Permuting two-coordinate chunks, while preserving the order inside each
chunk, preserves the Pfaffian even when the chunks have nonzero cross-couplings.
Arbitrary fixed coordinates may precede and follow the permuted chunks. -/
theorem pfaffianList_pairChunks_perm (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x)
    {xs ys : List (ι × ι)} (hperm : xs.Perm ys) (pre suf : List ι) :
    pfaffianList A (pre ++ xs.flatMap (fun p => [p.1, p.2]) ++ suf) =
      pfaffianList A (pre ++ ys.flatMap (fun p => [p.1, p.2]) ++ suf) := by
  induction hperm generalizing pre with
  | nil => rfl
  | @cons p xs ys hperm ih =>
    simpa only [List.flatMap_cons, List.append_assoc] using ih (pre ++ [p.1, p.2])
  | swap p q xs =>
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc] using
      pfaffianList_swap_pairChunks A hskew q.1 q.2 p.1 p.2 pre
        (xs.flatMap (fun p => [p.1, p.2]) ++ suf)
  | trans _ _ ih₁ ih₂ => exact (ih₁ pre).trans (ih₂ pre)

end MatchgateWidth
