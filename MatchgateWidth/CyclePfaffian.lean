import MatchgateWidth.PfaffianBlocks

/-!
# Alternating-cycle components

The local matrix used in Theorem 7.1 of arXiv:2610.00079v1 consists of
unit-weight consecutive edges and the upper-right entry `y - 1`.
The arguments below use the recursive ordered Pfaffian directly.
-/

namespace MatchgateWidth

variable {R ι : Type*} [CommRing R]

/-- A forced first edge can be removed from the ordered Pfaffian. -/
theorem pfaffianList_forced_first (A : Matrix ι ι R) (a b : ι) (xs : List ι)
    (hzero : ∀ x ∈ xs, A a x = 0) :
    pfaffianList A (a :: b :: xs) = A a b * pfaffianList A xs := by
  rw [pfaffianList]
  simp only [List.length_cons]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_mul,
    List.eraseIdx_zero]
  have h : (∑ i : Fin xs.length,
      (-1 : R) ^ i.succ.val * A a (b :: xs)[i.succ] *
        pfaffianList A ((b :: xs).eraseIdx i.succ.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show (b :: xs)[i.succ] = xs[i] by simp]
    rw [hzero xs[i] (List.getElem_mem i.isLt)]
    simp
  rw [h, add_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Expansion when only the first and last entries of the first row can be nonzero. -/
theorem pfaffianList_first_last (A : Matrix ι ι R) (a b z : ι) (xs : List ι)
    (hzero : ∀ x ∈ xs, A a x = 0) :
    pfaffianList A (a :: b :: (xs ++ [z])) =
      A a b * pfaffianList A (xs ++ [z]) +
        (-1 : R) ^ (xs.length + 1) * A a z * pfaffianList A (b :: xs) := by
  rw [pfaffianList]
  let f : Fin (b :: (xs ++ [z])).length → R := fun j =>
    (-1 : R) ^ j.val * A a (b :: (xs ++ [z]))[j] *
      pfaffianList A ((b :: (xs ++ [z])).eraseIdx j.val)
  change (∑ j, f j) = _
  have hlen : (b :: (xs ++ [z])).length = (xs.length + 1) + 1 := by simp
  rw [← Fin.sum_congr' f hlen.symm, Fin.sum_univ_succ,
    Fin.sum_univ_castSucc]
  dsimp [f]
  have hz : (∑ i : Fin xs.length,
      (-1 : R) ^ (i.val + 1) *
        A a ((xs ++ [z])[i.val]'(by simp; omega)) *
        pfaffianList A (b :: (xs ++ [z]).eraseIdx i.val)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [List.getElem_append_left i.isLt]
    have hv := hzero (xs[i.val]) (List.getElem_mem i.isLt)
    rw [hv]
    simp
  rw [hz]
  simp [List.eraseIdx_append_of_length_le]

/-- A matrix whose upper entries are exactly the unit-weight path edges. -/
def pathMatrix : Matrix ℕ ℕ R := fun i j =>
  if i + 1 = j then 1 else if j + 1 = i then -1 else 0

/-- On every consecutive interval of even length the path Pfaffian is one. -/
theorem pathMatrix_pfaffian_range (s n : ℕ) :
    pfaffianList (pathMatrix : Matrix ℕ ℕ R) (List.range' s (2 * n)) = 1 := by
  induction n generalizing s with
  | zero => simp [List.range']
  | succ n ih =>
    have hlen : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [hlen]
    change pfaffianList pathMatrix
      (s :: (s + 1) :: List.range' (s + 1 + 1) (2 * n)) = 1
    rw [pfaffianList_forced_first]
    · simp [pathMatrix, ih]
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
      simp only [Nat.one_mul]
      have h₁ : ¬s + 1 = s + 1 + 1 + i := by omega
      have h₂ : ¬s + 1 + 1 + i + 1 = s := by omega
      simp [pathMatrix, h₁, h₂]

/-- The skew-symmetric alternating-cycle component on the ordered modes
`0,...,2*n-1`. The singleton component has its own edge of weight `y`. -/
def cycleComponent (n : ℕ) (y : R) : Matrix ℕ ℕ R := fun i j =>
  if n = 1 then
    if i = 0 ∧ j = 1 then y else if i = 1 ∧ j = 0 then -y else 0
  else if i = 0 ∧ j + 1 = 2 * n then y - 1
  else if j = 0 ∧ i + 1 = 2 * n then -(y - 1)
  else pathMatrix i j

@[simp] theorem cycleComponent_singleton (y : R) :
    pfaffianList (cycleComponent 1 y) [0,1] = y := by
  simp [cycleComponent]

@[simp] theorem cycleComponent_empty (n : ℕ) (y : R) :
    pfaffianList (cycleComponent n y) [] = 1 := by simp

/-- Away from mode zero the cycle agrees with the unit-weight path. -/
theorem cycleComponent_eq_path_of_pos (n i j : ℕ) (y : R)
    (hn : 2 ≤ n) (hi : 0 < i) (hj : 0 < j) :
    cycleComponent n y i j = pathMatrix i j := by
  simp [cycleComponent, show n ≠ 1 by omega, show i ≠ 0 by omega,
    show j ≠ 0 by omega]

/-- Consecutive positive-mode intervals have path Pfaffian one. -/
theorem cycleComponent_pfaffian_positive_range (n s m : ℕ) (y : R)
    (hn : 2 ≤ n) (hs : 0 < s) :
    pfaffianList (cycleComponent n y) (List.range' s (2 * m)) = 1 := by
  rw [pfaffianList_congr (cycleComponent n y) pathMatrix (List.range' s (2 * m))]
  · exact pathMatrix_pfaffian_range s m
  · intro i hi j hj
    obtain ⟨a, ha, rfl⟩ := List.mem_range'.mp hi
    obtain ⟨b, hb, rfl⟩ := List.mem_range'.mp hj
    apply cycleComponent_eq_path_of_pos n _ _ y hn <;> omega

/-- Full selection of a non-singleton alternating-cycle component has Pfaffian `y`.
Both terms of the recursion have positive sign, including when `y - 1 = 0`. -/
theorem cycleComponent_pfaffian_full_add_two (n : ℕ) (y : R) :
    pfaffianList (cycleComponent (n + 2) y) (List.range' 0 (2 * (n + 2))) = y := by
  have hlist : List.range' 0 (2 * (n + 2)) =
      0 :: 1 :: (List.range' 2 (2 * n + 1) ++ [2 * n + 3]) := by
    have he : 2 * (n + 2) = (2 * n + 2) + 1 + 1 := by omega
    rw [he, List.range'_succ, List.range'_succ]
    simp only [Nat.zero_add]
    congr 2
    have he' : 2 * n + 2 = (2 * n + 1) + 1 := by omega
    rw [he', List.range'_1_concat]
    congr 1
    congr 1
    omega
  rw [hlist, pfaffianList_first_last]
  · have hleft : List.range' 2 (2 * n + 1) ++ [2 * n + 3] =
        List.range' 2 (2 * (n + 1)) := by
      have he : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [he, List.range'_1_concat (s := 2) (n := 2 * n + 1)]
      congr 2; omega
    have hright : 1 :: List.range' 2 (2 * n + 1) =
        List.range' 1 (2 * (n + 1)) := by
      have he : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [he]
      exact (List.range'_succ (s := 1) (n := 2 * n + 1) (step := 1)).symm
    rw [hleft, hright, cycleComponent_pfaffian_positive_range _ _ _ y (by omega) (by omega),
      cycleComponent_pfaffian_positive_range _ _ _ y (by omega) (by omega)]
    have hbase : cycleComponent (n + 2) y 0 1 = 1 := by
      simp [cycleComponent, pathMatrix, show n + 2 ≠ 1 by omega,
        show ¬1 + 1 = 2 * (n + 2) by omega]
    have hclose : cycleComponent (n + 2) y 0 (2 * n + 3) = y - 1 := by
      simp [cycleComponent, show n + 2 ≠ 1 by omega,
        show 2 * n + 3 + 1 = 2 * (n + 2) by omega]
    rw [hbase, hclose]
    simp only [List.length_range', mul_one]
    have hexp : 2 * n + 1 + 1 = 2 * (n + 1) := by omega
    rw [hexp, pow_mul]
    simp
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx
    simp only [Nat.one_mul]
    simp [cycleComponent, pathMatrix, show n + 2 ≠ 1 by omega,
      show ¬2 + i + 1 = 2 * (n + 2) by omega,
      show ¬0 + 1 = 2 + i by omega]

/-- Full selection of any nonempty component has Pfaffian `y`. -/
theorem cycleComponent_pfaffian_full (n : ℕ) (y : R) (hn : 0 < n) :
    pfaffianList (cycleComponent n y) (List.range' 0 (2 * n)) = y := by
  rcases n with _ | n
  · omega
  rcases n with _ | n
  · exact cycleComponent_singleton y
  · exact cycleComponent_pfaffian_full_add_two n y

/-- Select whole consecutive mode-pairs according to a Boolean mask. -/
def selectedPairModes (s : ℕ) : List Bool → List ℕ
  | [] => []
  | false :: bs => selectedPairModes (s + 2) bs
  | true :: bs => s :: (s + 1) :: selectedPairModes (s + 2) bs

@[simp] theorem selectedPairModes_length (s : ℕ) (bs : List Bool) :
    (selectedPairModes s bs).length = 2 * bs.count true := by
  induction bs generalizing s with
  | nil => simp [selectedPairModes]
  | cons b bs ih => cases b <;> simp [selectedPairModes, ih, Nat.mul_add]

/-- Every selected mode lies in the original consecutive interval. -/
theorem selectedPairModes_bounds (s x : ℕ) (bs : List Bool)
    (hx : x ∈ selectedPairModes s bs) : s ≤ x ∧ x < s + 2 * bs.length := by
  induction bs generalizing s with
  | nil => simp [selectedPairModes] at hx
  | cons b bs ih =>
    cases b
    · have h := ih (s + 2) hx
      simp only [List.length_cons]
      omega
    · simp only [selectedPairModes, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · simp
      · simp; omega
      · have h := ih (s + 2) hx
        simp only [List.length_cons]
        omega

/-- Pair selections respect concatenation, with the expected mode offset. -/
theorem selectedPairModes_append (s : ℕ) (as bs : List Bool) :
    selectedPairModes s (as ++ bs) =
      selectedPairModes s as ++ selectedPairModes (s + 2 * as.length) bs := by
  induction as generalizing s with
  | nil => simp [selectedPairModes]
  | cons a as ih =>
    cases a <;> simp only [List.cons_append, selectedPairModes, ih,
      List.length_cons, List.cons_append]
    · congr 2; omega
    · congr 4; omega

/-- Arbitrary selections of complete pairs have unit path Pfaffian. -/
theorem pathMatrix_pfaffian_selected_pairs (s : ℕ) (bs : List Bool) :
    pfaffianList (pathMatrix : Matrix ℕ ℕ R) (selectedPairModes s bs) = 1 := by
  induction bs generalizing s with
  | nil => simp [selectedPairModes]
  | cons b bs ih =>
    cases b
    · exact ih (s + 2)
    · rw [selectedPairModes, pfaffianList_forced_first]
      · simp [pathMatrix, ih]
      · intro x hx
        have h := selectedPairModes_bounds (s + 2) x bs hx
        simp [pathMatrix, show ¬s + 1 = x by omega, show ¬x + 1 = s by omega]

/-- An alternating path whose endpoints are half-pairs contributes only when
all its interior pairs are present. -/
theorem pathMatrix_pfaffian_bridge (s : ℕ) (bs : List Bool) :
    pfaffianList (pathMatrix : Matrix ℕ ℕ R)
      (s :: (selectedPairModes (s + 1) bs ++ [s + 2 * bs.length + 1])) =
        if bs.all id then 1 else 0 := by
  induction bs generalizing s with
  | nil => simp [selectedPairModes, pathMatrix]
  | cons b bs ih =>
    cases b
    · simp only [selectedPairModes, List.length_cons, List.all_cons,
        id_eq, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      apply pfaffianList_isolated_first
      intro j
      have hx := List.getElem_mem j.isLt
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | hx
      · have hb := selectedPairModes_bounds (s + 1 + 2) _ bs hx
        change pathMatrix s ((selectedPairModes (s + 1 + 2) bs ++
          [s + 2 * (bs.length + 1) + 1])[j.val]) = 0
        simp only [pathMatrix]
        split_ifs <;> first | omega | rfl
      · change pathMatrix s ((selectedPairModes (s + 1 + 2) bs ++
          [s + 2 * (bs.length + 1) + 1])[j.val]) = 0
        rw [hx]
        simp [pathMatrix, show ¬s + 2 * (bs.length + 1) + 1 + 1 = s by omega]
    · simp only [selectedPairModes, List.cons_append, List.length_cons,
        List.all_cons, id_eq, Bool.true_and]
      rw [pfaffianList_forced_first]
      · have he : s + 2 * (bs.length + 1) + 1 = (s + 1 + 1) + 2 * bs.length + 1 := by omega
        have hs : s + 1 + 2 = (s + 1 + 1) + 1 := by omega
        rw [he, hs, ih]
        simp [pathMatrix]
      · intro x hx
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | hx | rfl
        · simp [pathMatrix, show ¬s + 1 + 1 + 1 = s by omega]
        · have hb := selectedPairModes_bounds (s + 1 + 2) x bs hx
          simp [pathMatrix, show ¬s + 1 = x by omega, show ¬x + 1 = s by omega]
        · simp [pathMatrix, show ¬s + 2 * (bs.length + 1) + 1 + 1 = s by omega]

/-- Restricting to positive modes removes the closing edge. -/
theorem cycleComponent_pfaffian_eq_path (n : ℕ) (y : R) (xs : List ℕ)
    (hn : 2 ≤ n) (hpos : ∀ x ∈ xs, 0 < x) :
    pfaffianList (cycleComponent n y) xs = pfaffianList pathMatrix xs := by
  apply pfaffianList_congr
  intro i hi j hj
  exact cycleComponent_eq_path_of_pos n i j y hn (hpos i hi) (hpos j hj)

/-- Internal modes other than the first neighbor have zero first-row entries. -/
theorem cycleComponent_first_internal (n x : ℕ) (y : R)
    (hn : 2 ≤ n) (hx : 2 ≤ x) (hxn : x + 1 < 2 * n) :
    cycleComponent n y 0 x = 0 := by
  simp [cycleComponent, pathMatrix, show n ≠ 1 by omega,
    show ¬x + 1 = 2 * n by omega, show x ≠ 0 by omega,
    show ¬1 = x by omega]

/-- With both endpoint pairs present, the correction term survives exactly
when every interior pair is also selected. -/
theorem cycleComponent_pfaffian_endpoints (bs : List Bool) (y : R) :
    pfaffianList (cycleComponent (bs.length + 2) y)
      (selectedPairModes 0 (true :: (bs ++ [true]))) =
        if bs.all id then y else 1 := by
  let a := 2 + 2 * bs.length
  let z := a + 1
  let xs := selectedPairModes 2 bs ++ [a]
  have hlist : selectedPairModes 0 (true :: (bs ++ [true])) =
      0 :: 1 :: (xs ++ [z]) := by
    simp [selectedPairModes, selectedPairModes_append, xs, z, a, List.append_assoc]
  have hxs : ∀ x ∈ xs, 2 ≤ x ∧ x ≤ a := by
    intro x hx
    simp only [xs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · have hb := selectedPairModes_bounds 2 x bs hx
      dsimp [a]
      omega
    · dsimp [a]; omega
  rw [hlist, pfaffianList_first_last]
  · have hleft : pfaffianList (cycleComponent (bs.length + 2) y) (xs ++ [z]) = 1 := by
      rw [cycleComponent_pfaffian_eq_path _ _ _ (by omega)]
      · have he : xs ++ [z] = selectedPairModes 2 (bs ++ [true]) := by
          simp [selectedPairModes_append, selectedPairModes, xs, z, a, List.append_assoc]
        rw [he, pathMatrix_pfaffian_selected_pairs]
      · intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact lt_of_lt_of_le (by omega) (hxs x hx).1
        · dsimp [z, a]; omega
    have hright : pfaffianList (cycleComponent (bs.length + 2) y) (1 :: xs) =
        if bs.all id then 1 else 0 := by
      rw [cycleComponent_pfaffian_eq_path _ _ _ (by omega)]
      · have he : a = 1 + 2 * bs.length + 1 := by dsimp [a]; omega
        change pfaffianList pathMatrix (1 :: (selectedPairModes 2 bs ++ [a])) = _
        rw [he]
        exact pathMatrix_pfaffian_bridge 1 bs
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · omega
        · exact lt_of_lt_of_le (by omega) (hxs x hx).1
    rw [hleft, hright]
    have hbase : cycleComponent (bs.length + 2) y 0 1 = 1 := by
      simp [cycleComponent, pathMatrix, show bs.length + 2 ≠ 1 by omega,
        show ¬1 + 1 = 2 * (bs.length + 2) by omega]
    have hclose : cycleComponent (bs.length + 2) y 0 z = y - 1 := by
      have hz : z + 1 = 2 * (bs.length + 2) := by dsimp [z, a]; omega
      simp [cycleComponent, hz, show bs.length + 2 ≠ 1 by omega]
    have hsign : (-1 : R) ^ (xs.length + 1) = 1 := by
      have he : xs.length + 1 = 2 * (bs.count true + 1) := by
        simp [xs, Nat.mul_add]
      rw [he, pow_mul]
      simp
    rw [hbase, hclose, hsign]
    split_ifs <;> ring
  · intro x hx
    have hb := hxs x hx
    apply cycleComponent_first_internal _ _ y (by omega) hb.1
    dsimp [a] at hb
    omega

/-- Omitting the last pair forces the baseline term. -/
theorem cycleComponent_pfaffian_missing_last (bs : List Bool) (y : R) :
    pfaffianList (cycleComponent (bs.length + 2) y)
      (selectedPairModes 0 (true :: (bs ++ [false]))) = 1 := by
  have hlist : selectedPairModes 0 (true :: (bs ++ [false])) =
      0 :: 1 :: selectedPairModes 2 bs := by
    simp [selectedPairModes, selectedPairModes_append]
  rw [hlist, pfaffianList_forced_first]
  · have hbase : cycleComponent (bs.length + 2) y 0 1 = 1 := by
      simp [cycleComponent, pathMatrix, show bs.length + 2 ≠ 1 by omega,
        show ¬1 + 1 = 2 * (bs.length + 2) by omega]
    rw [hbase, one_mul, cycleComponent_pfaffian_eq_path _ _ _ (by omega)]
    · exact pathMatrix_pfaffian_selected_pairs 2 bs
    · intro x hx
      have hb := selectedPairModes_bounds 2 x bs hx
      omega
  · intro x hx
    have hb := selectedPairModes_bounds 2 x bs hx
    exact cycleComponent_first_internal _ _ y (by omega) hb.1 (by omega)

/-- The component contribution for every whole-pair selection: `y` for the
full selection and `1` otherwise. No classification of matchings is assumed. -/
theorem cycleComponent_pfaffian_selected_pairs (bs : List Bool) (y : R)
    (hne : bs ≠ []) :
    pfaffianList (cycleComponent bs.length y) (selectedPairModes 0 bs) =
      if bs.all id then y else 1 := by
  cases bs with
  | nil => exact False.elim (hne rfl)
  | cons b bs =>
    cases b
    · cases bs with
      | nil => simp [selectedPairModes]
      | cons b bs =>
        simp only [selectedPairModes, List.all_cons, id_eq, Bool.false_and,
          Bool.false_eq_true, ↓reduceIte]
        rw [cycleComponent_pfaffian_eq_path _ _ _ (by simp)]
        · exact pathMatrix_pfaffian_selected_pairs 2 (b :: bs)
        · intro x hx
          have hb := selectedPairModes_bounds 2 x (b :: bs) hx
          omega
    · rcases List.eq_nil_or_concat bs with rfl | ⟨cs, b, rfl⟩
      · exact cycleComponent_singleton y
      · cases b
        · simpa [List.concat_eq_append, List.all_append] using
            cycleComponent_pfaffian_missing_last cs y
        · simpa [List.concat_eq_append, List.all_append] using
            cycleComponent_pfaffian_endpoints cs y

/-- In particular, every proper selection of complete pairs has Pfaffian one. -/
theorem cycleComponent_pfaffian_proper_pairs (bs : List Bool) (y : R)
    (hproper : bs.all id = false) :
    pfaffianList (cycleComponent bs.length y) (selectedPairModes 0 bs) = 1 := by
  have hne : bs ≠ [] := by intro h; simp [h] at hproper
  rw [cycleComponent_pfaffian_selected_pairs bs y hne, hproper]
  rfl

/-- The path matrix has the required reverse-edge signs. -/
theorem pathMatrix_skew (i j : ℕ) :
    (pathMatrix : Matrix ℕ ℕ R) j i = -pathMatrix i j := by
  by_cases hij : i + 1 = j
  · have hji : ¬j + 1 = i := by omega
    simp [pathMatrix, hij, hji]
  · by_cases hji : j + 1 = i
    · simp [pathMatrix, hij, hji]
    · simp [pathMatrix, hij, hji]

/-- All reverse entries of the component are fixed by skew-symmetry. -/
theorem cycleComponent_skew (n i j : ℕ) (y : R) :
    cycleComponent n y j i = -cycleComponent n y i j := by
  unfold cycleComponent
  split_ifs <;> try omega
  all_goals try simp only [neg_neg, neg_zero]
  all_goals exact pathMatrix_skew i j

/-- The diagonal is zero even over rings of characteristic two. -/
@[simp] theorem cycleComponent_diag (n i : ℕ) (y : R) :
    cycleComponent n y i i = 0 := by
  have h₁ : ¬(i = 0 ∧ i = 1) := by omega
  have h₂ : ¬(i = 1 ∧ i = 0) := by omega
  have h₃ : ¬(i = 0 ∧ i + 1 = 2 * n) := by omega
  simp [cycleComponent, pathMatrix, h₁, h₂, h₃]

/-- Every baseline edge of a non-singleton component has weight one. -/
theorem cycleComponent_baseline (n i : ℕ) (y : R) (hn : 2 ≤ n) (_hi : i < n) :
    cycleComponent n y (2 * i) (2 * i + 1) = 1 := by
  have hc : ¬(2 * i = 0 ∧ 2 * i + 1 + 1 = 2 * n) := by omega
  simp only [cycleComponent, ite_eq_right (show n ≠ 1 by omega), ite_eq_right hc]
  simp [pathMatrix]

/-- Every consecutive alternate edge has weight one. -/
theorem cycleComponent_alternate (n i : ℕ) (y : R) (hn : 2 ≤ n)
    (_hi : i + 1 < n) :
    cycleComponent n y (2 * i + 1) (2 * i + 2) = 1 := by
  simp [cycleComponent, pathMatrix, show n ≠ 1 by omega, Nat.add_assoc]

/-- The final alternate edge has weight `y - 1`. -/
theorem cycleComponent_closing (n : ℕ) (y : R) (hn : 2 ≤ n) :
    cycleComponent n y 0 (2 * n - 1) = y - 1 := by
  simp [cycleComponent, show n ≠ 1 by omega, show 2 * n - 1 + 1 = 2 * n by omega]

/-- The selected modes are in the inherited strict order, without repetitions. -/
theorem selectedPairModes_pairwise (s : ℕ) (bs : List Bool) :
    (selectedPairModes s bs).Pairwise (· < ·) := by
  induction bs generalizing s with
  | nil => simp [selectedPairModes]
  | cons b bs ih =>
    cases b
    · exact ih (s + 2)
    · simp only [selectedPairModes, List.pairwise_cons, List.mem_cons]
      refine ⟨?_, ?_, ih (s + 2)⟩
      · intro x hx
        rcases hx with rfl | hx
        · omega
        · have hb := selectedPairModes_bounds (s + 2) x bs hx
          omega
      · intro x hx
        have hb := selectedPairModes_bounds (s + 2) x bs hx
        omega

/-- The actual finite matrix on `2*n` ordered modes. -/
def finiteCycleComponent (n : ℕ) (y : R) : Matrix (Fin (2 * n)) (Fin (2 * n)) R :=
  fun i j => cycleComponent n y i.val j.val

/-- A Boolean whole-pair selection, now typed in the finite component. -/
def selectedPairModesFin (bs : List Bool) : List (Fin (2 * bs.length)) :=
  (selectedPairModes 0 bs).pmap (fun x hx => ⟨x, hx⟩)
    (fun x hx => by have hb := selectedPairModes_bounds 0 x bs hx; omega)

@[simp] theorem selectedPairModesFin_map_val (bs : List Bool) :
    (selectedPairModesFin bs).map Fin.val = selectedPairModes 0 bs := by
  simp [selectedPairModesFin, List.map_pmap, List.pmap_eq_map]

/-- The finite component satisfies the same complete selection law. -/
theorem finiteCycleComponent_pfaffian_selected_pairs (bs : List Bool) (y : R)
    (hne : bs ≠ []) :
    pfaffianList (finiteCycleComponent bs.length y) (selectedPairModesFin bs) =
      if bs.all id then y else 1 := by
  rw [show finiteCycleComponent bs.length y =
    (fun i j : Fin (2 * bs.length) => cycleComponent bs.length y (Fin.val i) (Fin.val j)) from rfl,
    ← pfaffianList_map, selectedPairModesFin_map_val]
  exact cycleComponent_pfaffian_selected_pairs bs y hne

/-- The finite matrix is skew-symmetric. -/
theorem finiteCycleComponent_skew (n : ℕ) (y : R) (i j : Fin (2 * n)) :
    finiteCycleComponent n y j i = -finiteCycleComponent n y i j :=
  cycleComponent_skew n i.val j.val y

/-- The increasing complete list of the component's finite modes. -/
def fullCycleModes (n : ℕ) : List (Fin (2 * n)) :=
  (List.range' 0 (2 * n)).pmap (fun x hx => ⟨x, hx⟩)
    (fun x hx => by obtain ⟨i, hi, rfl⟩ := List.mem_range'.mp hx; simpa using hi)

@[simp] theorem fullCycleModes_map_val (n : ℕ) :
    (fullCycleModes n).map Fin.val = List.range' 0 (2 * n) := by
  simp [fullCycleModes, List.map_pmap, List.pmap_eq_map]

/-- The actual finite matrix's full ordered Pfaffian is the prescribed parameter. -/
theorem finiteCycleComponent_pfaffian_full (n : ℕ) (y : R) (hn : 0 < n) :
    pfaffianList (finiteCycleComponent n y) (fullCycleModes n) = y := by
  change pfaffianList (fun i j : Fin (2 * n) => cycleComponent n y i.val j.val)
    (fullCycleModes n) = y
  rw [← pfaffianList_map, fullCycleModes_map_val]
  exact cycleComponent_pfaffian_full n y hn

/-- Proper selections in the finite matrix have unit Pfaffian. -/
theorem finiteCycleComponent_pfaffian_proper_pairs (bs : List Bool) (y : R)
    (hproper : bs.all id = false) :
    pfaffianList (finiteCycleComponent bs.length y) (selectedPairModesFin bs) = 1 := by
  have hne : bs ≠ [] := by intro h; simp [h] at hproper
  rw [finiteCycleComponent_pfaffian_selected_pairs bs y hne, hproper]
  rfl

/-- Canonical mask of a subset of the component's baseline pairs. -/
def componentPairMask (n : ℕ) (T : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ T))

@[simp] theorem componentPairMask_length (n : ℕ) (T : Finset (Fin n)) :
    (componentPairMask n T).length = n := by simp [componentPairMask]

/-- The mask is full precisely when every baseline pair is selected. -/
theorem componentPairMask_all (n : ℕ) (T : Finset (Fin n)) :
    (componentPairMask n T).all id = true ↔ T = Finset.univ := by
  rw [List.all_eq_true]
  constructor
  · intro h
    apply Finset.eq_univ_of_forall
    intro i
    have hi : decide (i ∈ T) ∈ componentPairMask n T := by
      exact List.mem_ofFn.mpr ⟨i, rfl⟩
    simpa using h (decide (i ∈ T)) hi
  · intro h x hx
    subst T
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp

/-- Whole-pair selection law stated directly for an arbitrary subset of `Fin n`. -/
theorem cycleComponent_pfaffian_pair_subset (n : ℕ) (T : Finset (Fin n))
    (y : R) (hn : 0 < n) :
    pfaffianList (cycleComponent n y) (selectedPairModes 0 (componentPairMask n T)) =
      if T = Finset.univ then y else 1 := by
  have hne : componentPairMask n T ≠ [] := by
    apply List.length_pos_iff.mp
    simpa using hn
  have h := cycleComponent_pfaffian_selected_pairs (componentPairMask n T) y hne
  simpa only [componentPairMask_length, componentPairMask_all] using h

/-- Every proper subset of the full baseline-pair set contributes one. -/
theorem cycleComponent_pfaffian_proper_subset (n : ℕ) (T : Finset (Fin n))
    (y : R) (hT : T ≠ Finset.univ) :
    pfaffianList (cycleComponent n y) (selectedPairModes 0 (componentPairMask n T)) = 1 := by
  have hmask : (componentPairMask n T).all id = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    exact hT ((componentPairMask_all n T).mp h)
  have h := cycleComponent_pfaffian_proper_pairs (componentPairMask n T) y hmask
  simpa only [componentPairMask_length] using h

end MatchgateWidth
