import MatchgateWidth.PfaffianIdentities

/-!
# Exact single-edge updates of ordered principal Pfaffians

All formulas here use the actual recursive Pfaffian. The two updated modes are
moved to the front by the proved alternating law, and the first-row recurrence
then isolates their new entry. Coefficients may lie in any commutative ring.
No matching expansion or graphical realization is assumed.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

section Unordered

variable [DecidableEq ι]

/-- Add `t` at `(i,j)` and subtract it at `(j,i)`. The definition also makes
sense for `i = j`, in which case the two increments cancel. -/
def pfaffianEdgeUpdate (A : Matrix ι ι R) (i j : ι) (t : R) : Matrix ι ι R :=
  fun x y => A x y + (if x = i ∧ y = j then t else 0) -
    (if x = j ∧ y = i then t else 0)

@[simp] theorem pfaffianEdgeUpdate_forward (A : Matrix ι ι R)
    {i j : ι} (hij : i ≠ j) (t : R) :
    pfaffianEdgeUpdate A i j t i j = A i j + t := by
  simp [pfaffianEdgeUpdate, hij]

@[simp] theorem pfaffianEdgeUpdate_reverse (A : Matrix ι ι R)
    {i j : ι} (hij : i ≠ j) (t : R) :
    pfaffianEdgeUpdate A i j t j i = A j i - t := by
  simp [pfaffianEdgeUpdate, hij, Ne.symm hij]

@[simp] theorem pfaffianEdgeUpdate_diag (A : Matrix ι ι R)
    (i j x : ι) (t : R) :
    pfaffianEdgeUpdate A i j t x x = A x x := by
  simp only [pfaffianEdgeUpdate, and_comm (a := x = i) (b := x = j)]
  ring

theorem pfaffianEdgeUpdate_skew (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (i j : ι) (t : R) :
    ∀ x y, pfaffianEdgeUpdate A i j t x y =
      -pfaffianEdgeUpdate A i j t y x := by
  intro x y
  simp only [pfaffianEdgeUpdate, hskew x y]
  simp only [and_comm (a := y = i) (b := x = j),
    and_comm (a := y = j) (b := x = i)]
  ring

/-- If either updated mode is absent, the entire selected Pfaffian is unchanged.
No skewness or distinctness hypotheses are needed for this locality statement. -/
theorem pfaffianList_edgeUpdate_of_not_mem (A : Matrix ι ι R)
    (i j : ι) (t : R) (xs : List ι) (h : i ∉ xs ∨ j ∉ xs) :
    pfaffianList (pfaffianEdgeUpdate A i j t) xs = pfaffianList A xs := by
  apply pfaffianList_congr
  intro x hx y hy
  rcases h with hi | hj
  · have hxi : x ≠ i := fun e => hi (e ▸ hx)
    have hyi : y ≠ i := fun e => hi (e ▸ hy)
    simp [pfaffianEdgeUpdate, hxi, hyi]
  · have hxj : x ≠ j := fun e => hj (e ▸ hx)
    have hyj : y ≠ j := fun e => hj (e ▸ hy)
    simp [pfaffianEdgeUpdate, hxj, hyj]

omit [DecidableEq ι] in
private theorem signedEraseSum_congr_sublist (f g : ι → R)
    (F G : List ι → R) (xs : List ι)
    (hf : ∀ x ∈ xs, f x = g x)
    (hF : ∀ ys, ys.Sublist xs → F ys = G ys) :
    signedEraseSum f F xs = signedEraseSum g G xs := by
  induction xs generalizing F G with
  | nil => rfl
  | cons x xs ih =>
    simp only [signedEraseSum]
    rw [hf x (by simp), hF xs (List.sublist_cons_self _ _)]
    rw [ih]
    · intro y hy
      exact hf y (by simp [hy])
    · intro ys hy
      exact hF (x :: ys) (hy.cons_cons x)

/-- When the changed edge is the first selected pair, its contribution is exactly
`t` times the remaining Pfaffian. -/
theorem pfaffianList_edgeUpdate_head_pair (A : Matrix ι ι R)
    {i j : ι} (hij : i ≠ j) (t : R) (xs : List ι)
    (hi : i ∉ xs) (hj : j ∉ xs) :
    pfaffianList (pfaffianEdgeUpdate A i j t) (i :: j :: xs) =
      pfaffianList A (i :: j :: xs) + t * pfaffianList A xs := by
  rw [pfaffianList_cons_signedEraseSum (pfaffianEdgeUpdate A i j t) i,
    pfaffianList_cons_signedEraseSum A i]
  simp only [signedEraseSum]
  rw [pfaffianEdgeUpdate_forward A hij t]
  have htail : signedEraseSum (pfaffianEdgeUpdate A i j t i)
      (fun ys => pfaffianList (pfaffianEdgeUpdate A i j t) (j :: ys)) xs =
      signedEraseSum (A i) (fun ys => pfaffianList A (j :: ys)) xs := by
    apply signedEraseSum_congr_sublist
    · intro x hx
      have hxj : x ≠ j := fun e => hj (e ▸ hx)
      simp [pfaffianEdgeUpdate, hij, hxj]
    · intro ys hys
      apply pfaffianList_edgeUpdate_of_not_mem
      apply Or.inl
      simp only [List.mem_cons, not_or]
      exact ⟨hij, fun h => hi (hys.subset h)⟩
  rw [htail]
  have hxs := pfaffianList_edgeUpdate_of_not_mem A i j t xs (Or.inl hi)
  simpa only [pfaffianList_cons_signedEraseSum] using
    (show (A i j + t) * pfaffianList (pfaffianEdgeUpdate A i j t) xs -
        signedEraseSum (A i) (fun ys => pfaffianList A (j :: ys)) xs =
      A i j * pfaffianList A xs -
        signedEraseSum (A i) (fun ys => pfaffianList A (j :: ys)) xs +
        t * pfaffianList A xs by rw [hxs]; ring)

omit [DecidableEq ι] in
/-- Bring two selected positions to the front. If their zero-based positions are
`p < q`, the exponent is `q - p - 1`, the number of positions between them. -/
theorem pfaffianList_move_pair_front (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (i j : ι)
    (pre middle suf : List ι) :
    pfaffianList A (pre ++ i :: (middle ++ j :: suf)) =
      (-1 : R) ^ middle.length *
        pfaffianList A (i :: j :: (pre ++ middle ++ suf)) := by
  have hi := pfaffianList_move_right A hskew i pre [] (middle ++ j :: suf)
  have hj := pfaffianList_move_right A hskew j (pre ++ middle) [i] suf
  simp only [List.nil_append, List.cons_append, List.append_assoc,
    List.length_append] at hi hj
  simp only [List.append_assoc]
  rw [hj, hi]
  rw [pow_add]
  have hp : (-1 : R) ^ pre.length * (-1 : R) ^ pre.length = 1 := by
    rw [← mul_pow]; simp
  have hm : (-1 : R) ^ middle.length * (-1 : R) ^ middle.length = 1 := by
    rw [← mul_pow]; simp
  calc
    _ = (1 : R) * (1 : R) *
        pfaffianList A (pre ++ i :: (middle ++ j :: suf)) := by simp
    _ = ((-1 : R) ^ pre.length * (-1 : R) ^ pre.length) *
        ((-1 : R) ^ middle.length * (-1 : R) ^ middle.length) *
        pfaffianList A (pre ++ i :: (middle ++ j :: suf)) := by rw [hp, hm]
    _ = _ := by ring

/-- Exact ordered edge-update formula. Distinct updated modes must be absent
from the prefix, intervening list, and suffix; other repeated modes are allowed. -/
theorem pfaffianList_edgeUpdate (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) {i j : ι} (hij : i ≠ j)
    (t : R) (pre middle suf : List ι)
    (hi : i ∉ pre ++ middle ++ suf) (hj : j ∉ pre ++ middle ++ suf) :
    pfaffianList (pfaffianEdgeUpdate A i j t)
        (pre ++ i :: (middle ++ j :: suf)) =
      pfaffianList A (pre ++ i :: (middle ++ j :: suf)) +
        (-1 : R) ^ middle.length * t * pfaffianList A (pre ++ middle ++ suf) := by
  rw [pfaffianList_move_pair_front _ (pfaffianEdgeUpdate_skew A hskew i j t),
    pfaffianList_move_pair_front A hskew,
    pfaffianList_edgeUpdate_head_pair A hij t _ hi hj]
  ring

/-- Adjacent selected modes contribute with positive sign, wherever they occur. -/
theorem pfaffianList_edgeUpdate_adjacent (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) {i j : ι} (hij : i ≠ j)
    (t : R) (pre suf : List ι) (hi : i ∉ pre ++ suf) (hj : j ∉ pre ++ suf) :
    pfaffianList (pfaffianEdgeUpdate A i j t) (pre ++ i :: j :: suf) =
      pfaffianList A (pre ++ i :: j :: suf) + t * pfaffianList A (pre ++ suf) := by
  simpa using pfaffianList_edgeUpdate A hskew hij t pre [] suf (by simpa using hi) (by simpa using hj)

end Unordered

section Ordered

variable [LinearOrder ι]

private theorem edgeUpdate_sort_insert (S : Finset ι) (a : ι) (ha : a ∉ S) :
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

private theorem pfaffianList_insert_sort_prefix (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (S : Finset ι) (a : ι)
    (ha : a ∉ S) (pre : List ι) :
    pfaffianList A (pre ++ a :: S.sort (· ≤ ·)) =
      (-1 : R) ^ (S.filter (· < a)).card *
        pfaffianList A (pre ++ (insert a S).sort (· ≤ ·)) := by
  have hlength : ((S.sort (· ≤ ·)).filter (fun x => decide (x < a))).length =
      (S.filter (· < a)).card := by
    rw [← List.toFinset_card_of_nodup
      (List.Nodup.filter _ (Finset.sort_nodup S (· ≤ ·)))]
    simp [List.toFinset_filter]
  rw [edgeUpdate_sort_insert S a ha, ← hlength]
  exact pfaffianList_orderedInsert A hskew a (S.sort (· ≤ ·))
    (Finset.pairwise_sort S (· ≤ ·)) pre

private theorem edgeUpdate_filter_erase_self (S : Finset ι) (i : ι) :
    (S.erase i).filter (· < i) = S.filter (· < i) := by
  rw [Finset.filter_erase]
  apply Finset.erase_eq_of_notMem
  simp

/-- Sign obtained by bringing `i`, then `j`, to the front of an increasing
selected set. For `i < j` at zero-based selected positions `p < q`, this is
`(-1)^(p + q - 1)`, equivalently `(-1)^(q - p - 1)`. -/
def pfaffianPairCreationSign (S : Finset ι) (i j : ι) : R :=
  (-1 : R) ^ ((S.filter (· < i)).card + ((S.erase i).filter (· < j)).card)

/-- Consecutive selected modes have positive pair-creation sign. -/
theorem pfaffianPairCreationSign_of_no_between (S : Finset ι) {i j : ι}
    (hij : i < j) (hgap : ∀ k ∈ S, ¬(i < k ∧ k < j)) :
    pfaffianPairCreationSign (R := R) S i j = 1 := by
  have hfilter : (S.erase i).filter (· < j) = S.filter (· < i) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hki, hk⟩, hkj⟩
      refine ⟨hk, ?_⟩
      rcases lt_trichotomy k i with h | h | h
      · exact h
      · exact (hki h).elim
      · exact (hgap k hk ⟨h, hkj⟩).elim
    · rintro ⟨hk, hki⟩
      exact ⟨⟨ne_of_lt hki, hk⟩, hki.trans hij⟩
  simp only [pfaffianPairCreationSign, hfilter, pow_add, ← mul_pow]
  simp

theorem pfaffianList_pair_sort (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (S : Finset ι)
    {i j : ι} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) :
    pfaffianList A (i :: j :: ((S.erase i).erase j).sort (· ≤ ·)) =
      pfaffianPairCreationSign S i j * pfaffianList A (S.sort (· ≤ ·)) := by
  have hji : j ∈ S.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have h := pfaffianList_insert_sort_prefix A hskew ((S.erase i).erase j) j
    (by simp) [i]
  simp only [List.cons_append, List.nil_append] at h
  rw [h, Finset.insert_erase hji, pfaffianList_insert_sort A hskew (S.erase i) i
    (by simp), Finset.insert_erase hi]
  rw [edgeUpdate_filter_erase_self, edgeUpdate_filter_erase_self]
  simp only [pfaffianPairCreationSign, pow_add]
  ring

/-- The uniform finite-set version of the exact edge-update formula, with the
sign expressed by the two selected positions before and after deleting `i`. -/
theorem pfaffianList_edgeUpdate_sort (A : Matrix ι ι R)
    (hskew : ∀ x y, A x y = -A y x) (S : Finset ι)
    {i j : ι} (hij : i ≠ j) (hi : i ∈ S) (hj : j ∈ S) (t : R) :
    pfaffianList (pfaffianEdgeUpdate A i j t) (S.sort (· ≤ ·)) =
      pfaffianList A (S.sort (· ≤ ·)) + pfaffianPairCreationSign S i j * t *
        pfaffianList A (((S.erase i).erase j).sort (· ≤ ·)) := by
  have h := pfaffianList_edgeUpdate_head_pair A hij t
    (((S.erase i).erase j).sort (· ≤ ·)) (by simp) (by simp)
  rw [pfaffianList_pair_sort _ (pfaffianEdgeUpdate_skew A hskew i j t)
    S hij hi hj, pfaffianList_pair_sort A hskew S hij hi hj] at h
  have hs : pfaffianPairCreationSign (R := R) S i j *
      pfaffianPairCreationSign S i j = 1 := by
    unfold pfaffianPairCreationSign
    rw [← mul_pow]; simp
  calc
    _ = pfaffianPairCreationSign S i j *
        (pfaffianPairCreationSign S i j *
          pfaffianList (pfaffianEdgeUpdate A i j t) (S.sort (· ≤ ·))) := by
      rw [← mul_assoc, hs, one_mul]
    _ = _ := by rw [h]; simp only [mul_add, ← mul_assoc, hs, one_mul]

end Ordered

/-- Pair creation on the entire principal-Pfaffian table. A selected coordinate
changes only when it contains both modes, and then refers to their deletion. -/
def pfaffianPairCreation {s : ℕ} (i j : Fin s) (t : R)
    (F : SubsetSignature s R) : SubsetSignature s R := fun S =>
  F S + if i ∈ S ∧ j ∈ S then
    pfaffianPairCreationSign S i j * t * F ((S.erase i).erase j) else 0

/-- Matrix edge addition is exactly the pair-creation operator on every
principal-Pfaffian coordinate simultaneously. -/
theorem principalPfaffian_edgeUpdate {s : ℕ} (A : Matrix (Fin s) (Fin s) R)
    (hskew : ∀ x y, A x y = -A y x) {i j : Fin s} (hij : i ≠ j) (t : R) :
    principalPfaffian (pfaffianEdgeUpdate A i j t) =
      pfaffianPairCreation i j t (principalPfaffian A) := by
  funext S
  by_cases h : i ∈ S ∧ j ∈ S
  · simp only [pfaffianPairCreation, ite_eq_left h, principalPfaffian]
    exact pfaffianList_edgeUpdate_sort A hskew S hij h.1 h.2 t
  · simp only [pfaffianPairCreation, ite_eq_right h, add_zero, principalPfaffian]
    apply pfaffianList_edgeUpdate_of_not_mem
    simpa using not_and_or.mp h

/-- On neighboring boundary modes, pair creation is the elementary unsigned
update `F(S) += t * F(S \ {i,j})` when both modes are selected. -/
theorem pfaffianPairCreation_adjacent {s : ℕ} (i j : Fin s)
    (hij : j.val = i.val + 1) (t : R) (F : SubsetSignature s R) (S : Finset (Fin s)) :
    pfaffianPairCreation i j t F S =
      F S + if i ∈ S ∧ j ∈ S then t * F ((S.erase i).erase j) else 0 := by
  have hs : pfaffianPairCreationSign (R := R) S i j = 1 := by
    apply pfaffianPairCreationSign_of_no_between S (by omega)
    intro k _ hk
    have hi := hk.1
    have hj := hk.2
    simp only [Fin.lt_def] at hi hj
    omega
  simp only [pfaffianPairCreation, hs, one_mul]

/-- The empty-mode state: only its empty selected coordinate is nonzero. -/
def pfaffianVacuum {s : ℕ} : SubsetSignature s R :=
  fun S => if S = ∅ then 1 else 0

@[simp] theorem principalPfaffian_zero {s : ℕ} :
    principalPfaffian (0 : Matrix (Fin s) (Fin s) R) = pfaffianVacuum := by
  funext S
  by_cases hS : S = ∅
  · simp [principalPfaffian, pfaffianVacuum, hS]
  · have hn : S.sort (· ≤ ·) ≠ [] := by
      intro hs
      apply hS
      simpa using congrArg List.toFinset hs
    obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hn
    simp only [pfaffianVacuum, ite_eq_right hS, principalPfaffian, hx]
    exact pfaffianList_isolated_first _ x xs (by simp)

/-- Build a matrix by adding the listed strict upper-triangular entries of `A`.
The recursion applies the tail first, fixing an explicit circuit order. -/
def pfaffianEdgeBuildMatrix {s : ℕ} (A : Matrix (Fin s) (Fin s) R) :
    List (PfaffianUpperPair s) → Matrix (Fin s) (Fin s) R
  | [] => 0
  | p :: ps => pfaffianEdgeUpdate (pfaffianEdgeBuildMatrix A ps)
      p.val.1 p.val.2 (A p.val.1 p.val.2)

/-- Apply those same pair-creation steps to the vacuum table. -/
def pfaffianEdgeBuildTable {s : ℕ} (A : Matrix (Fin s) (Fin s) R) :
    List (PfaffianUpperPair s) → SubsetSignature s R
  | [] => pfaffianVacuum
  | p :: ps => pfaffianPairCreation p.val.1 p.val.2 (A p.val.1 p.val.2)
      (pfaffianEdgeBuildTable A ps)

theorem pfaffianEdgeBuildMatrix_skew {s : ℕ} (A : Matrix (Fin s) (Fin s) R)
    (ps : List (PfaffianUpperPair s)) :
    ∀ x y, pfaffianEdgeBuildMatrix A ps x y = -pfaffianEdgeBuildMatrix A ps y x := by
  induction ps with
  | nil => simp [pfaffianEdgeBuildMatrix]
  | cons p ps ih =>
    exact pfaffianEdgeUpdate_skew _ ih _ _ _

@[simp] theorem pfaffianEdgeBuildMatrix_diag {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (ps : List (PfaffianUpperPair s)) (x : Fin s) :
    pfaffianEdgeBuildMatrix A ps x x = 0 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [pfaffianEdgeBuildMatrix, pfaffianEdgeUpdate_diag] using ih

/-- The matrix/table invariant holds after every finite list of edge updates,
including repetitions and arbitrary upper-entry weights. -/
theorem pfaffianEdgeBuildTable_eq {s : ℕ} (A : Matrix (Fin s) (Fin s) R)
    (ps : List (PfaffianUpperPair s)) :
    pfaffianEdgeBuildTable A ps = principalPfaffian (pfaffianEdgeBuildMatrix A ps) := by
  induction ps with
  | nil => exact principalPfaffian_zero.symm
  | cons p ps ih =>
    simp only [pfaffianEdgeBuildTable, pfaffianEdgeBuildMatrix, ih]
    exact (principalPfaffian_edgeUpdate _ (pfaffianEdgeBuildMatrix_skew A ps)
      (ne_of_lt p.property) _).symm

private theorem pfaffianEdgeBuildMatrix_eq_sum {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (ps : List (PfaffianUpperPair s)) :
    pfaffianEdgeBuildMatrix A ps =
      (ps.map (fun p => pfaffianEdgeUpdate (0 : Matrix (Fin s) (Fin s) R)
        p.val.1 p.val.2 (A p.val.1 p.val.2))).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [pfaffianEdgeBuildMatrix, List.map_cons, List.sum_cons, ih]
    funext x y
    simp [pfaffianEdgeUpdate]
    ring

private theorem pfaffianEdgeBuildMatrix_all_upper {s : ℕ}
    (A : Matrix (Fin s) (Fin s) R) (x y : Fin s) (hxy : x < y) :
    pfaffianEdgeBuildMatrix A (Finset.univ.toList : List (PfaffianUpperPair s)) x y =
      A x y := by
  rw [pfaffianEdgeBuildMatrix_eq_sum,
    ← List.sum_toFinset _ (Finset.nodup_toList _), Finset.toList_toFinset]
  simp only [Matrix.sum_apply]
  let q : PfaffianUpperPair s := ⟨(x, y), hxy⟩
  rw [Finset.sum_eq_single q]
  · simp [q, pfaffianEdgeUpdate, ne_of_lt hxy, ne_of_gt hxy]
  · intro p _ hp
    have hforward : ¬(x = p.val.1 ∧ y = p.val.2) := by
      rintro ⟨hx, hy⟩
      apply hp
      exact Subtype.ext (Prod.ext hx.symm hy.symm)
    have hreverse : ¬(x = p.val.2 ∧ y = p.val.1) := by
      rintro ⟨hx, hy⟩
      have hp := p.property
      rw [← hx, ← hy] at hp
      exact (not_lt_of_gt hxy) hp
    simp [pfaffianEdgeUpdate, hforward, hreverse]
  · simp

/-- Adding each strict upper-triangular edge once reconstructs every alternating
matrix, with no assumption on the characteristic of the coefficient ring. -/
theorem pfaffianEdgeBuildMatrix_all {s : ℕ} (A : Matrix (Fin s) (Fin s) R)
    (hskew : ∀ x y, A x y = -A y x) (hdiag : ∀ x, A x x = 0) :
    pfaffianEdgeBuildMatrix A (Finset.univ.toList : List (PfaffianUpperPair s)) = A := by
  funext x y
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact pfaffianEdgeBuildMatrix_all_upper A x y hxy
  · simp [hdiag]
  · rw [pfaffianEdgeBuildMatrix_skew,
      pfaffianEdgeBuildMatrix_all_upper A y x hyx]
    exact (hskew x y).symm

/-- A constructive algebraic synthesis of the entire principal-Pfaffian table:
start with the vacuum and apply one signed pair-creation update per upper edge.
This theorem alone makes no assertion of planar graphical realization. -/
theorem pfaffianEdgeBuildTable_all {s : ℕ} (A : Matrix (Fin s) (Fin s) R)
    (hskew : ∀ x y, A x y = -A y x) (hdiag : ∀ x, A x x = 0) :
    pfaffianEdgeBuildTable A (Finset.univ.toList : List (PfaffianUpperPair s)) =
      principalPfaffian A := by
  rw [pfaffianEdgeBuildTable_eq, pfaffianEdgeBuildMatrix_all A hskew hdiag]

end MatchgateWidth
