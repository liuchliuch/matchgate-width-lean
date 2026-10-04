import MatchgateWidth.PfaffianPermutation
import Mathlib.Data.List.Sort
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# The signed pair-partition definition of the Pfaffian

A pair partition is represented by its pairs in increasing order of their first
entries, with the smaller entry first in each pair. The finite enumeration below
chooses the partner of the smallest remaining entry. Its soundness, completeness,
and lack of repetitions are proved, rather than assumed. The sign of a partition
is the parity of the inversions in its flattened pair sequence, exactly the
convention of equation (pfaffian-definition) in the source paper.
-/

namespace MatchgateWidth

variable {ι R : Type*}

/-- The sequence `(u₁,v₁,…,uₘ,vₘ)` associated to an ordered pair partition. -/
def pairSequence (ps : List (ι × ι)) : List ι :=
  ps.flatMap (fun p => [p.1, p.2])

@[simp] theorem pairSequence_nil : pairSequence ([] : List (ι × ι)) = [] := rfl

@[simp] theorem pairSequence_cons (p : ι × ι) (ps : List (ι × ι)) :
    pairSequence (p :: ps) = p.1 :: p.2 :: pairSequence ps := rfl

/-- Enumerate pair partitions by choosing the partner of the first remaining
entry. For an increasing input, every pair and the list of first entries are
increasing. An odd-sized input has no pair partitions. -/
def pairPartitions : List ι → List (List (ι × ι))
  | [] => [[]]
  | a :: xs => (List.ofFn (fun j : Fin xs.length =>
      (pairPartitions (xs.eraseIdx j.val)).map (fun ps => (a, xs[j]) :: ps))).flatten
termination_by xs => xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_eraseIdx_le ..)

@[simp] theorem pairPartitions_nil : pairPartitions ([] : List ι) = [[]] :=
  pairPartitions.eq_1

@[simp] theorem mem_pairPartitions_cons {a : ι} {xs : List ι} {ps : List (ι × ι)} :
    ps ∈ pairPartitions (a :: xs) ↔
      ∃ j : Fin xs.length, ∃ qs ∈ pairPartitions (xs.eraseIdx j.val),
        (a, xs[j]) :: qs = ps := by
  rw [pairPartitions]
  constructor
  · intro h
    obtain ⟨ls, hls, hp⟩ := List.mem_flatten.mp h
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hls
    obtain ⟨qs, hqs, rfl⟩ := List.mem_map.mp hp
    exact ⟨j, qs, hqs, rfl⟩
  · rintro ⟨j, qs, hqs, rfl⟩
    exact List.mem_flatten.mpr ⟨_, List.mem_ofFn.mpr ⟨j, rfl⟩,
      List.mem_map.mpr ⟨qs, hqs, rfl⟩⟩

/-- Every enumerated pair partition uses every input entry exactly once. -/
theorem pairSequence_perm_of_mem_pairPartitions {xs : List ι}
    {ps : List (ι × ι)} (h : ps ∈ pairPartitions xs) :
    (pairSequence ps).Perm xs := by
  induction xs using (measure List.length).wf.induction generalizing ps with
  | _ xs ih =>
    cases xs with
    | nil =>
      have : ps = [] := by simpa using h
      subst ps
      simp
    | cons a xs =>
      obtain ⟨j, qs, hqs, rfl⟩ := mem_pairPartitions_cons.mp h
      have hr := ih (xs.eraseIdx j.val)
        (Nat.lt_succ_of_le (List.length_eraseIdx_le ..)) hqs
      exact (hr.cons xs[j]).trans (List.getElem_cons_eraseIdx_perm j.isLt) |>.cons a

section LinearOrder
variable [LinearOrder ι]

/-- The usual inversion count: pairs of positions whose entries occur in
strictly decreasing order. -/
def pairInversions : List ι → ℕ
  | [] => 0
  | a :: xs => xs.countP (fun b => decide (b < a)) + pairInversions xs

/-- Canonical pair order: each pair is increasing and each pair's first entry
is smaller than every entry in the later pairs. This is equivalent to the
paper's increasing order of first entries together with increasing pairs. -/
def CanonicalPairs : List (ι × ι) → Prop
  | [] => True
  | p :: ps => p.1 < p.2 ∧
      (∀ z ∈ pairSequence ps, p.1 < z) ∧ CanonicalPairs ps

/-- The canonical condition is exactly the two ordering conventions in the
paper: each pair is increasing, and first entries increase from pair to pair. -/
theorem canonicalPairs_iff_increasing (ps : List (ι × ι)) :
    CanonicalPairs ps ↔
      (∀ p ∈ ps, p.1 < p.2) ∧ (ps.map Prod.fst).Pairwise (· < ·) := by
  induction ps with
  | nil => simp [CanonicalPairs]
  | cons p ps ih =>
    simp only [CanonicalPairs, List.map_cons, List.pairwise_cons]
    constructor
    · rintro ⟨hp, hrest, hc⟩
      obtain ⟨hpairs, hheads⟩ := ih.mp hc
      refine ⟨?_, ?_, hheads⟩
      · intro q hq
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hpairs q hq
      · intro z hz
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
        exact hrest q.1 (List.mem_flatMap.mpr ⟨q, hq, by simp⟩)
    · rintro ⟨hpairs, hhead, hheads⟩
      refine ⟨hpairs p (by simp), ?_, ih.mpr ⟨?_, hheads⟩⟩
      · intro z hz
        obtain ⟨q, hq, hz⟩ := List.mem_flatMap.mp hz
        have hpq : p.1 < q.1 := hhead q.1 (List.mem_map.mpr ⟨q, hq, rfl⟩)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact hpq
        · exact hpq.trans (hpairs q (by simp [hq]))
      · intro q hq
        exact hpairs q (by simp [hq])

omit [LinearOrder ι] in
private theorem countP_eq_sum_fin (p : ι → Bool) (xs : List ι) :
    xs.countP p = ∑ j : Fin xs.length, if p xs[j] then 1 else 0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.countP_cons, List.length_cons, Fin.sum_univ_succ,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ]
    simp only [Fin.getElem_fin] at ih
    rw [ih, Nat.add_comm]
    rfl

/-- Inversion count is literally the number of position pairs `i < j` with
`xs[j] < xs[i]`, rather than a separately assigned recursive sign. -/
theorem pairInversions_eq_sum_positions (xs : List ι) :
    pairInversions xs = ∑ i : Fin xs.length, ∑ j : Fin xs.length,
      if i < j ∧ xs[j] < xs[i] then 1 else 0 := by
  induction xs with
  | nil => simp [pairInversions]
  | cons a xs ih =>
    simp only [pairInversions, List.length_cons, Fin.sum_univ_succ]
    simp only [Fin.not_lt_zero, false_and, ↓reduceIte, zero_add,
      Fin.succ_pos, true_and, Fin.succ_lt_succ_iff,
      Fin.getElem_fin, Fin.val_zero, Fin.val_succ, List.getElem_cons_zero,
      List.getElem_cons_succ]
    rw [countP_eq_sum_fin, ih]
    simp only [decide_eq_true_eq, Fin.getElem_fin]

/-- Enumeration chooses precisely the canonical orientation and pair order. -/
theorem canonicalPairs_of_mem_pairPartitions {xs : List ι}
    (hs : xs.Pairwise (· < ·)) {ps : List (ι × ι)}
    (h : ps ∈ pairPartitions xs) : CanonicalPairs ps := by
  induction xs using (measure List.length).wf.induction generalizing ps with
  | _ xs ih =>
    cases xs with
    | nil =>
      have : ps = [] := by simpa using h
      subst ps
      simp [CanonicalPairs]
    | cons a xs =>
      obtain ⟨j, qs, hqs, rfl⟩ := mem_pairPartitions_cons.mp h
      obtain ⟨ha, hxs⟩ := List.pairwise_cons.mp hs
      refine ⟨ha _ (List.getElem_mem j.isLt), ?_, ?_⟩
      · intro z hz
        exact ha z (List.mem_of_mem_eraseIdx
          ((pairSequence_perm_of_mem_pairPartitions hqs).mem_iff.mp hz))
      · exact ih _ (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
          (hxs.sublist (List.eraseIdx_sublist ..)) hqs

/-- Every canonical pair partition of an increasing list occurs in the
first-partner enumeration. -/
theorem mem_pairPartitions_of_canonicalPairs {xs : List ι}
    (hs : xs.Pairwise (· < ·)) {ps : List (ι × ι)}
    (hc : CanonicalPairs ps) (hp : (pairSequence ps).Perm xs) :
    ps ∈ pairPartitions xs := by
  induction xs using (measure List.length).wf.induction generalizing ps with
  | _ xs ih =>
    cases ps with
    | nil =>
      have hx : [] = xs := hp.nil_eq
      subst xs
      simp
    | cons p qs =>
      rcases p with ⟨u, v⟩
      cases xs with
      | nil => simp at hp
      | cons a xs =>
        obtain ⟨ha, hxs⟩ := List.pairwise_cons.mp hs
        obtain ⟨huv, huqs, hqs⟩ := hc
        have hua : u = a := by
          apply le_antisymm
          · have ham : a ∈ u :: v :: pairSequence qs :=
              hp.mem_iff.mpr (by simp)
            rcases List.mem_cons.mp ham with rfl | ham
            · exact le_rfl
            rcases List.mem_cons.mp ham with rfl | ham
            · exact le_of_lt huv
            · exact le_of_lt (huqs a ham)
          · have hum : u ∈ a :: xs := hp.mem_iff.mp (by simp)
            rcases List.mem_cons.mp hum with rfl | hum
            · exact le_rfl
            · exact le_of_lt (ha u hum)
        subst u
        have ht : (v :: pairSequence qs).Perm xs := hp.cons_inv
        have hvm : v ∈ xs := ht.mem_iff.mp (by simp)
        obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hvm
        let j : Fin xs.length := ⟨k, hk⟩
        have hv : xs[j] = v := hkv
        have hr : (pairSequence qs).Perm (xs.eraseIdx j.val) := by
          have hremove := List.getElem_cons_eraseIdx_perm j.isLt
          simp only [Fin.getElem_fin] at hv
          rw [hv] at hremove
          exact (ht.trans hremove.symm).cons_inv
        apply mem_pairPartitions_cons.mpr
        refine ⟨j, qs, ih _ (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
          (hxs.sublist (List.eraseIdx_sublist ..)) hqs hr, ?_⟩
        simp only [hv]

/-- Exact, nonrecursive characterization of the enumerated pair partitions. -/
theorem mem_pairPartitions_iff {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} :
    ps ∈ pairPartitions xs ↔ CanonicalPairs ps ∧ (pairSequence ps).Perm xs :=
  ⟨fun h => ⟨canonicalPairs_of_mem_pairPartitions hs h,
      pairSequence_perm_of_mem_pairPartitions h⟩,
    fun h => mem_pairPartitions_of_canonicalPairs hs h.1 h.2⟩

/-- No canonical pair partition is counted more than once. -/
theorem nodup_pairPartitions {xs : List ι} (hs : xs.Pairwise (· < ·)) :
    (pairPartitions xs).Nodup := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp
    | cons a xs =>
      obtain ⟨_, hxs⟩ := List.pairwise_cons.mp hs
      rw [pairPartitions, List.nodup_flatten]
      constructor
      · intro ls hls
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hls
        exact List.Nodup.map (fun _ _ h => List.cons.inj h |>.2)
          (ih _ (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
            (hxs.sublist (List.eraseIdx_sublist ..)))
      · apply List.pairwise_ofFn.mpr
        intro j k hjk ps hpj hpk
        obtain ⟨qs, _, heqj⟩ := List.mem_map.mp hpj
        obtain ⟨rs, _, heqk⟩ := List.mem_map.mp hpk
        have heq : xs[j] = xs[k] := by
          exact congrArg Prod.snd ((List.cons.inj (heqj.trans heqk.symm)).1)
        have heqidx : j.val = k.val := hxs.nodup.getElem_inj_iff.mp heq
        exact (ne_of_lt hjk) (Fin.ext heqidx)

private theorem countP_lt_eraseIdx {xs : List ι} (hs : xs.Pairwise (· < ·))
    (j : Fin xs.length) :
    (xs.eraseIdx j.val).countP (fun z => decide (z < xs[j])) = j.val := by
  induction xs with
  | nil => exact Fin.elim0 j
  | cons a xs ih =>
    obtain ⟨ha, hxs⟩ := List.pairwise_cons.mp hs
    refine Fin.cases ?_ (fun k => ?_) j
    · simp only [Fin.val_zero, List.eraseIdx_zero, Fin.getElem_fin, List.getElem_cons_zero]
      apply List.countP_eq_zero.mpr
      intro z hz
      simp [not_lt_of_gt (ha z hz)]
    · simp only [Fin.val_succ, List.eraseIdx_cons_succ, Fin.getElem_fin,
        List.getElem_cons_succ, List.countP_cons]
      have hi := ih hxs k
      simp only [Fin.getElem_fin] at hi
      rw [hi]
      simp [ha _ (List.getElem_mem k.isLt)]

/-- Removing the first pair contributes exactly the partner's index to the
inversion count; this is the sign in the recursive first-row expansion. -/
theorem pairInversions_cons_pair {a : ι} {xs : List ι}
    (hs : (a :: xs).Pairwise (· < ·)) (j : Fin xs.length)
    {qs : List (ι × ι)} (hqs : qs ∈ pairPartitions (xs.eraseIdx j.val)) :
    pairInversions (pairSequence ((a, xs[j]) :: qs)) =
      j.val + pairInversions (pairSequence qs) := by
  obtain ⟨ha, hxs⟩ := List.pairwise_cons.mp hs
  have hp := pairSequence_perm_of_mem_pairPartitions hqs
  have hzero : (xs[j] :: pairSequence qs).countP (fun z => decide (z < a)) = 0 := by
    apply List.countP_eq_zero.mpr
    intro z hz
    have hzxs : z ∈ xs := by
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.getElem_mem j.isLt
      · exact List.mem_of_mem_eraseIdx (hp.mem_iff.mp hz)
    simpa using not_lt_of_gt (ha z hzxs)
  simp only [pairSequence_cons, pairInversions, hzero, zero_add]
  rw [hp.countP_eq, countP_lt_eraseIdx hxs j]

/-- The finite set of pair partitions. -/
def canonicalPairPartitions (xs : List ι) : Finset (List (ι × ι)) :=
  (pairPartitions xs).toFinset

/-- Membership in the finite index set is precisely the source definition:
pairs oriented increasingly, increasing first entries, and exact coverage. -/
theorem mem_canonicalPairPartitions {xs : List ι} (hs : xs.Pairwise (· < ·))
    {ps : List (ι × ι)} :
    ps ∈ canonicalPairPartitions xs ↔
      (∀ p ∈ ps, p.1 < p.2) ∧ (ps.map Prod.fst).Pairwise (· < ·) ∧
      (pairSequence ps).Perm xs := by
  simp only [canonicalPairPartitions, List.mem_toFinset,
    mem_pairPartitions_iff hs, canonicalPairs_iff_increasing, and_assoc]

variable [CommRing R]

/-- A perfect-matching monomial: one matrix entry per pair. -/
def pairMonomial (A : Matrix ι ι R) (ps : List (ι × ι)) : R :=
  (ps.map (fun p => A p.1 p.2)).prod

/-- The signed pair-partition term using the inversion-count sign. -/
def signedPairMonomial (A : Matrix ι ι R) (ps : List (ι × ι)) : R :=
  (-1 : R) ^ pairInversions (pairSequence ps) * pairMonomial A ps

/-- The source paper's finite signed sum over canonical pair partitions. -/
def pairPartitionPfaffian (A : Matrix ι ι R) (xs : List ι) : R :=
  ((pairPartitions xs).map (signedPairMonomial A)).sum

/-- The recursive Pfaffian is exactly the signed sum over pair partitions from
`eq:pfaffian-definition`. No skew-symmetry or even-order hypothesis is needed:
odd inputs give an empty sum, and the empty input contributes the empty product. -/
theorem pfaffianList_eq_pairPartitionPfaffian (A : Matrix ι ι R)
    {xs : List ι} (hs : xs.Pairwise (· < ·)) :
    pfaffianList A xs = pairPartitionPfaffian A xs := by
  induction xs using (measure List.length).wf.induction with
  | _ xs ih =>
    cases xs with
    | nil => simp [pairPartitionPfaffian, signedPairMonomial, pairInversions, pairMonomial]
    | cons a xs =>
      rw [pairPartitionPfaffian, pairPartitions, List.map_flatten, List.sum_flatten,
        List.map_map, List.map_ofFn, List.sum_ofFn, pfaffianList]
      apply Finset.sum_congr rfl
      intro j _
      have hi := ih (xs.eraseIdx j.val)
        (Nat.lt_succ_of_le (List.length_eraseIdx_le ..))
        ((List.pairwise_cons.mp hs).2.sublist (List.eraseIdx_sublist ..))
      rw [hi]
      dsimp [Function.comp_def]
      rw [List.map_map]
      have hterm : ∀ qs ∈ pairPartitions (xs.eraseIdx j.val),
          signedPairMonomial A ((a, xs[j]) :: qs) =
            ((-1 : R) ^ j.val * A a xs[j]) * signedPairMonomial A qs := by
        intro qs hqs
        simp only [signedPairMonomial, pairInversions_cons_pair hs j hqs,
          pairMonomial, List.map_cons, List.prod_cons, pow_add]
        ring
      simp only [Fin.getElem_fin] at hterm
      simp only [Function.comp_def]
      rw [List.map_congr_left hterm, List.sum_map_mul_left]
      rfl

/-- Explicit finite-sum form of the recursive-to-pair-partition bridge. -/
theorem pfaffianList_eq_sum_pairPartitions (A : Matrix ι ι R)
    {xs : List ι} (hs : xs.Pairwise (· < ·)) :
    pfaffianList A xs = ∑ ps ∈ canonicalPairPartitions xs,
      (-1 : R) ^ pairInversions (pairSequence ps) *
        (ps.map (fun p => A p.1 p.2)).prod := by
  rw [pfaffianList_eq_pairPartitionPfaffian A hs]
  symm
  exact List.sum_toFinset (signedPairMonomial A) (nodup_pairPartitions hs)

end LinearOrder
end MatchgateWidth
