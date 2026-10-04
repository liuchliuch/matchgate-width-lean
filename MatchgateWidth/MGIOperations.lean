import MatchgateWidth.MGITensor

/-!
# Ordered operations preserving the literal matchgate identities

All changes of coordinates below preserve the order of surviving ports. In
particular the contraction theorem joins two adjacent ports, not arbitrary
same-order boundary blocks.
-/

namespace MatchgateWidth
open scoped symmDiff

variable {R : Type*} [CommRing R]

theorem finset_map_symmDiff {s t : ℕ} (e : Fin s ↪ Fin t)
    (A B : Finset (Fin s)) :
    (A ∆ B).map e = A.map e ∆ B.map e := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases hi with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl ⟨⟨i, hA, rfl⟩, by rintro ⟨j, hj, he⟩; exact hB (e.injective he ▸ hj)⟩
    · exact Or.inr ⟨⟨i, hB, rfl⟩, by rintro ⟨j, hj, he⟩; exact hA (e.injective he ▸ hj)⟩
  · rintro (⟨⟨i, hi, rfl⟩, hn⟩ | ⟨⟨i, hi, rfl⟩, hn⟩)
    · exact ⟨i, Or.inl ⟨hi, fun h => hn ⟨i, h, rfl⟩⟩, rfl⟩
    · exact ⟨i, Or.inr ⟨hi, fun h => hn ⟨i, h, rfl⟩⟩, rfl⟩

theorem matchgateSum_map {s t : ℕ} (e : Fin s ↪ Fin t)
    (G : SubsetSignature t R) (A B : Finset (Fin s)) (p : List (Fin s)) :
    matchgateSum G (A.map e) (B.map e) (p.map e) =
      matchgateSum (fun S => G (S.map e)) A B p := by
  unfold matchgateSum
  apply Finset.sum_equiv (Fin.castOrderIso (List.length_map _)).toEquiv
  · simp
  · intro j _
    simp only [Fin.getElem_fin, List.getElem_map, finset_map_symmDiff,
      Finset.map_singleton]
    rfl

/-- Restricting a signature to any increasing subsequence of its coordinates,
with all omitted coordinates pinned to zero, preserves the exact identities. -/
theorem MatchgateIdentities.ordered_restrict {s t : ℕ}
    {G : SubsetSignature t R} (hG : MatchgateIdentities G)
    (e : Fin s ↪ Fin t) (he : StrictMono e) :
    MatchgateIdentities (fun S => G (S.map e)) := by
  intro A B
  have h := hG (A.map e) (B.map e)
  rw [← finset_map_symmDiff, ← Finset.map_sort e (A ∆ B) (· ≤ ·) (· ≤ ·)
    (fun a _ b _ => he.le_iff_le.symm)] at h
  simpa only [matchgateSum_map] using h

/-- An arbitrary fixed pattern on omitted coordinates can be pinned too.
The usual pinning interpretation takes `P` disjoint from the image of `e`. -/
theorem MatchgateIdentities.ordered_pin {s t : ℕ}
    {G : SubsetSignature t R} (hG : MatchgateIdentities G)
    (e : Fin s ↪ Fin t) (he : StrictMono e) (P : Finset (Fin t)) :
    MatchgateIdentities (fun S => G (S.map e ∆ P)) :=
  (hG.subsetPivot P).ordered_restrict e he

/-- Removing a two-element prefix does not change the signs of the remaining
MGI summands. -/
theorem matchgateSum_two_prefix {t : ℕ} (G : SubsetSignature t R)
    (A B : Finset (Fin t)) (a b : Fin t) (p : List (Fin t)) :
    matchgateSum G A B (a :: b :: p) =
      -G (A ∆ {a}) * G (B ∆ {a}) + G (A ∆ {b}) * G (B ∆ {b}) +
      matchgateSum G A B p := by
  unfold matchgateSum
  simp only [List.length_cons, Fin.sum_univ_succ]
  simp only [Fin.getElem_fin, Fin.val_zero, Fin.val_succ,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [pow_succ, pow_zero, one_mul, mul_neg, mul_one, neg_neg]
  ring

private theorem pair_xor_left {t : ℕ} (a b : Fin t) (hab : a ≠ b) :
    ({a, b} : Finset (Fin t)) ∆ {a} = {b} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  grind

private theorem pair_xor_right {t : ℕ} (a b : Fin t) (hab : a ≠ b) :
    ({a, b} : Finset (Fin t)) ∆ {b} = {a} := by
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  grind

/-- The four quadratic MGI expressions arising from adding two pinning
branches. The two mixed expressions use the same surviving difference list. -/
theorem matchgateSum_add_pair {t : ℕ} (G : SubsetSignature t R)
    (A B P : Finset (Fin t)) (p : List (Fin t)) :
    matchgateSum (fun S => G S + G (S ∆ P)) A B p =
      matchgateSum G A B p + matchgateSum G (A ∆ P) (B ∆ P) p +
      matchgateSum G A (B ∆ P) p + matchgateSum G (A ∆ P) B p := by
  simp only [matchgateSum, symmDiff_right_comm _ P, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Cancellation of the two mixed terms uses both MGI equations. Their two
adjacent prefix terms cancel pairwise, leaving the desired cross-term sum. -/
theorem MatchgateIdentities.mixed_pair_cancel {t : ℕ}
    {G : SubsetSignature t R} (hG : MatchgateIdentities G)
    (A B : Finset (Fin t)) (a b : Fin t) (hab : a ≠ b)
    (p : List (Fin t))
    (horder : ((A ∆ B) ∆ {a, b}).sort (· ≤ ·) = a :: b :: p) :
    matchgateSum G A (B ∆ {a, b}) p +
      matchgateSum G (A ∆ {a, b}) B p = 0 := by
  have h₁ := hG A (B ∆ {a, b})
  have h₂ := hG (A ∆ {a, b}) B
  rw [← symmDiff_assoc, horder, matchgateSum_two_prefix] at h₁
  rw [symmDiff_right_comm A {a, b} B, horder, matchgateSum_two_prefix] at h₂
  simp only [symmDiff_assoc, pair_xor_left a b hab, pair_xor_right a b hab] at h₁ h₂
  linear_combination h₁ + h₂

/-- A pair lying before every surviving port is the first two entries of the
sorted difference. -/
theorem sort_pair_prefix {t : ℕ} (D : Finset (Fin t)) (a b : Fin t)
    (hab : a < b) (hbD : ∀ x ∈ D, b < x) :
    (D ∆ {a, b}).sort (· ≤ ·) = a :: b :: D.sort (· ≤ ·) := by
  have hdis : Disjoint D {a, b} := by
    apply Finset.disjoint_left.mpr
    intro x hx hp
    rcases Finset.mem_insert.mp hp with he | he
    · subst x
      exact (lt_asymm hab (hbD a hx))
    · have he : x = b := Finset.mem_singleton.mp he
      subst x
      exact (lt_irrefl b (hbD b hx))
  have hset : D ∆ {a, b} = insert a (insert b D) := by
    rw [Finset.symmDiff_eq_union hdis]
    ext x
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hset, Finset.sort_insert (· ≤ ·), Finset.sort_insert (· ≤ ·)]
  · exact fun x hx => (hbD x hx).le
  · exact fun hx => lt_irrefl b (hbD b hx)
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hab.le
    · exact (hab.trans (hbD x hx)).le
  · simp only [Finset.mem_insert, not_or]
    exact ⟨hab.ne, fun hx => lt_asymm hab (hbD a hx)⟩

/-- Adding the zero-zero and one-one branches on two initial adjacent ports.
The surviving ports retain their original increasing order. -/
def adjacentPairContraction {s : ℕ} (G : SubsetSignature (2 + s) R) :
    SubsetSignature s R := fun S =>
  G (S.map (Fin.natAddEmb 2)) +
    G (S.map (Fin.natAddEmb 2) ∆ {⟨0, by omega⟩, ⟨1, by omega⟩})

/-- On the surviving coordinates, the two contracted ports are absent. Thus
the second branch is literally the union with the first two ports. -/
theorem adjacentPairContraction_apply {s : ℕ}
    (G : SubsetSignature (2 + s) R) (S : Finset (Fin s)) :
    adjacentPairContraction G S = G (S.map (Fin.natAddEmb 2)) +
      G (S.map (Fin.natAddEmb 2) ∪ {⟨0, by omega⟩, ⟨1, by omega⟩}) := by
  unfold adjacentPairContraction
  rw [Finset.symmDiff_eq_union]
  apply Finset.disjoint_left.mpr
  intro x hx hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with hp | hp
  · have hv := congrArg Fin.val hp
    change 2 + i.val = 0 at hv
    omega
  · have hv := congrArg Fin.val hp
    change 2 + i.val = 1 at hv
    omega

/-- Exact MGI closure under contraction of two adjacent first ports. The proof
uses the two pure-branch identities and cancellation between the two mixed
identities; no graphical realization or pre-assumed closure is used. -/
theorem MatchgateIdentities.adjacentPairContraction {s : ℕ}
    {G : SubsetSignature (2 + s) R} (hG : MatchgateIdentities G) :
    MatchgateIdentities (MatchgateWidth.adjacentPairContraction G) := by
  let e : Fin s ↪ Fin (2 + s) := Fin.natAddEmb 2
  let a : Fin (2 + s) := ⟨0, by omega⟩
  let b : Fin (2 + s) := ⟨1, by omega⟩
  have he : StrictMono e := Fin.strictMono_natAdd 2
  have hab : a < b := by change 0 < 1; omega
  intro A B
  let p := (A ∆ B).sort (· ≤ ·)
  have hp : ((A.map e ∆ B.map e) ∆ {a, b}).sort (· ≤ ·) =
      a :: b :: p.map e := by
    rw [← finset_map_symmDiff, sort_pair_prefix _ a b hab]
    · rw [← Finset.map_sort e (A ∆ B) (· ≤ ·) (· ≤ ·)
        (fun x _ y _ => he.le_iff_le.symm)]
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
      change 1 < 2 + i.val
      omega
  have hcross := hG.mixed_pair_cancel (A.map e) (B.map e) a b hab.ne (p.map e) hp
  have hzero := hG.ordered_restrict e he A B
  have hsame : matchgateSum G (A.map e ∆ {a, b}) (B.map e ∆ {a, b}) (p.map e) = 0 := by
    have h := (hG.subsetPivot {a, b}).ordered_restrict e he A B
    rw [← matchgateSum_map] at h
    simpa only [MatchgateWidth.subsetPivot, matchgateSum, symmDiff_right_comm _ {a, b}] using h
  have hzero' : matchgateSum G (A.map e) (B.map e) (p.map e) = 0 := by
    rw [matchgateSum_map]
    exact hzero
  have hadd := matchgateSum_add_pair G (A.map e) (B.map e) {a, b} (p.map e)
  rw [hzero', hsame, zero_add, zero_add, hcross] at hadd
  rw [matchgateSum_map] at hadd
  exact hadd

end MatchgateWidth
