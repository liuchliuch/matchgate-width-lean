import MatchgateWidth.MatchingSignature
import Mathlib.Data.Finset.Sum

/-!
# Weighted matching sums under disjoint union and bridge-edge gluing

The vertices and edges of the two component graphs retain disjoint identities.
Gluing adds a distinct unit-weight edge for every boundary index; it does not
identify vertices. The matching-sum identities below are proved by decomposing
finite edge subsets. No embedding or planar-closure hypothesis is assumed.
-/

namespace MatchgateWidth

noncomputable section

open Classical

variable {V W E F B K : Type*}
variable [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B]
variable [CommSemiring K]

/-- Disjoint union retaining both vertex and edge identities. -/
def disjointUnionGraph (G : WeightedGraph V E K) (H : WeightedGraph W F K) :
    WeightedGraph (V ⊕ W) (E ⊕ F) K where
  left := Sum.elim (fun e => Sum.inl (G.left e)) (fun f => Sum.inr (H.left f))
  right := Sum.elim (fun e => Sum.inl (G.right e)) (fun f => Sum.inr (H.right f))
  loopless := by
    rintro (e | f) h
    · exact G.loopless e (Sum.inl.inj h)
    · exact H.loopless f (Sum.inr.inj h)
  weight := Sum.elim G.weight H.weight

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [CommSemiring K] in
@[simp] theorem matchingDegree_disjointUnion_inl (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (m : Finset E) (n : Finset F) (v : V) :
    matchingDegree (disjointUnionGraph G H) (m.disjSum n) (Sum.inl v) =
      matchingDegree G m v := by
  classical
  simp [matchingDegree, Finset.sum_disjSum, disjointUnionGraph]

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [CommSemiring K] in
@[simp] theorem matchingDegree_disjointUnion_inr (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (m : Finset E) (n : Finset F) (w : W) :
    matchingDegree (disjointUnionGraph G H) (m.disjSum n) (Sum.inr w) =
      matchingDegree H n w := by
  classical
  simp [matchingDegree, Finset.sum_disjSum, disjointUnionGraph]

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [CommSemiring K] in
theorem matchesExactly_disjointUnion_iff (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (activeG : Finset V) (activeH : Finset W)
    (m : Finset E) (n : Finset F) :
    MatchesExactly (disjointUnionGraph G H) (activeG.disjSum activeH) (m.disjSum n) ↔
      MatchesExactly G activeG m ∧ MatchesExactly H activeH n := by
  classical
  simp only [MatchesExactly, Sum.forall, matchingDegree_disjointUnion_inl,
    matchingDegree_disjointUnion_inr, Finset.inl_mem_disjSum, Finset.inr_mem_disjSum]

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] in
@[simp] theorem matchingWeight_disjointUnion (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (m : Finset E) (n : Finset F) :
    (∏ e ∈ m.disjSum n, (disjointUnionGraph G H).weight e) =
      (∏ e ∈ m, G.weight e) * ∏ f ∈ n, H.weight f := by
  simp [Finset.prod_disjSum, disjointUnionGraph]

/-- The edge-set decomposition is an actual equivalence of finite types. -/
theorem sum_finset_disjSum {A C R : Type*} [Fintype A] [Fintype C]
    [AddCommMonoid R] (f : Finset (A ⊕ C) → R) :
    ∑ p, f p = ∑ a : Finset A, ∑ c : Finset C, f (a.disjSum c) := by
  classical
  rw [← (Finset.sumEquiv.toEquiv.symm).sum_comp f, Fintype.sum_prod_type]
  rfl

omit [Fintype V] [Fintype W] in
/-- Matching sums multiply under disjoint union, for arbitrary active sets. -/
theorem weightedPerfectMatch_disjointUnion (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (activeG : Finset V) (activeH : Finset W) :
    weightedPerfectMatch (disjointUnionGraph G H) (activeG.disjSum activeH) =
      weightedPerfectMatch G activeG * weightedPerfectMatch H activeH := by
  classical
  unfold weightedPerfectMatch
  rw [sum_finset_disjSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [matchesExactly_disjointUnion_iff, matchingWeight_disjointUnion]
  split_ifs <;> simp_all

/-- Add distinct unit-weight bridges between the indexed external vertices. -/
def bridgeGraph (G : WeightedGraph V E K) (H : WeightedGraph W F K)
    (extL : B → V) (extR : B → W) : WeightedGraph (V ⊕ W) ((E ⊕ F) ⊕ B) K where
  left := Sum.elim (disjointUnionGraph G H).left (fun b => Sum.inl (extL b))
  right := Sum.elim (disjointUnionGraph G H).right (fun b => Sum.inr (extR b))
  loopless := by
    rintro (e | b) h
    · exact (disjointUnionGraph G H).loopless e h
    · exact Sum.inl_ne_inr h
  weight := Sum.elim (disjointUnionGraph G H).weight (fun _ => 1)

/-- Remaining active vertices after the selected bridges cover their endpoints. -/
def bridgeRemaining (ext : B → V) (b : Finset B) : Finset V := by
  classical
  exact Finset.univ \ b.image ext

omit [Fintype V] [Fintype B] in
private theorem sum_incidence_injective (ext : B → V) (hext : Function.Injective ext)
    (b : Finset B) (v : V) :
    (∑ i ∈ b, if ext i = v then 1 else 0) =
      if v ∈ b.image ext then (1 : ℕ) else 0 := by
  classical
  rw [← Finset.sum_image (f := fun w => if w = v then (1 : ℕ) else 0)
    (s := b) (g := ext) (fun _ _ _ _ h => hext h)]
  simp

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B] in
@[simp] theorem matchingDegree_bridge_inl (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextL : Function.Injective extL) (m : Finset E) (n : Finset F)
    (b : Finset B) (v : V) :
    matchingDegree (bridgeGraph G H extL extR) ((m.disjSum n).disjSum b) (Sum.inl v) =
      matchingDegree G m v + if v ∈ b.image extL then 1 else 0 := by
  classical
  simp only [matchingDegree, Finset.sum_disjSum]
  simp only [bridgeGraph, disjointUnionGraph, Sum.elim_inl, Sum.elim_inr,
    Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte,
    add_zero, Finset.sum_const_zero]
  rw [sum_incidence_injective extL hextL]

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B] in
@[simp] theorem matchingDegree_bridge_inr (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextR : Function.Injective extR) (m : Finset E) (n : Finset F)
    (b : Finset B) (w : W) :
    matchingDegree (bridgeGraph G H extL extR) ((m.disjSum n).disjSum b) (Sum.inr w) =
      matchingDegree H n w + if w ∈ b.image extR then 1 else 0 := by
  classical
  simp only [matchingDegree, Finset.sum_disjSum]
  simp only [bridgeGraph, disjointUnionGraph, Sum.elim_inl, Sum.elim_inr,
    Sum.inr.injEq, Sum.inl_ne_inr, ↓reduceIte,
    add_zero, zero_add, Finset.sum_const_zero]
  rw [sum_incidence_injective extR hextR]

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B] in
/-- Decomposition with pre-existing vertex deletions, provided every bridge
endpoint is still active before gluing. -/
theorem matchesExactly_bridge_active_iff (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextL : Function.Injective extL) (hextR : Function.Injective extR)
    (activeG : Finset V) (activeH : Finset W)
    (hactiveL : ∀ i, extL i ∈ activeG) (hactiveR : ∀ i, extR i ∈ activeH)
    (m : Finset E) (n : Finset F) (b : Finset B) :
    MatchesExactly (bridgeGraph G H extL extR) (activeG.disjSum activeH)
        ((m.disjSum n).disjSum b) ↔
      MatchesExactly G (activeG \ b.image extL) m ∧
        MatchesExactly H (activeH \ b.image extR) n := by
  classical
  have hL : ∀ v, v ∈ b.image extL → v ∈ activeG := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact hactiveL i
  have hR : ∀ w, w ∈ b.image extR → w ∈ activeH := by
    intro w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    exact hactiveR i
  simp only [MatchesExactly, Sum.forall,
    matchingDegree_bridge_inl G H extL extR hextL,
    matchingDegree_bridge_inr G H extL extR hextR,
    Finset.inl_mem_disjSum, Finset.inr_mem_disjSum, Finset.mem_sdiff]
  constructor
  · rintro ⟨hm, hn⟩
    constructor
    · intro v
      have h := hm v
      have h' := hL v
      split_ifs at h ⊢ <;> simp_all
    · intro w
      have h := hn w
      have h' := hR w
      split_ifs at h ⊢ <;> simp_all
  · rintro ⟨hm, hn⟩
    constructor
    · intro v
      have h := hm v
      have h' := hL v
      split_ifs at h ⊢ <;> simp_all
    · intro w
      have h := hn w
      have h' := hR w
      split_ifs at h ⊢ <;> simp_all

omit [Fintype E] [Fintype F] [Fintype B] in
/-- The bridge choice determines exactly which component vertices are deleted. -/
theorem matchesExactly_bridge_iff (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextL : Function.Injective extL) (hextR : Function.Injective extR)
    (m : Finset E) (n : Finset F) (b : Finset B) :
    MatchesExactly (bridgeGraph G H extL extR) Finset.univ
        ((m.disjSum n).disjSum b) ↔
      MatchesExactly G (bridgeRemaining extL b) m ∧
        MatchesExactly H (bridgeRemaining extR b) n := by
  classical
  simp only [MatchesExactly, Sum.forall,
    matchingDegree_bridge_inl G H extL extR hextL,
    matchingDegree_bridge_inr G H extL extR hextR,
    Finset.mem_univ, ↓reduceIte, bridgeRemaining, Finset.mem_sdiff,
    true_and]
  constructor
  · rintro ⟨hL, hR⟩
    constructor
    · intro v
      have h := hL v
      split_ifs at h ⊢ <;> omega
    · intro w
      have h := hR w
      split_ifs at h ⊢ <;> omega
  · rintro ⟨hL, hR⟩
    constructor
    · intro v
      have h := hL v
      split_ifs at h ⊢ <;> omega
    · intro w
      have h := hR w
      split_ifs at h ⊢ <;> omega

omit [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B] in
@[simp] theorem matchingWeight_bridge (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (m : Finset E) (n : Finset F) (b : Finset B) :
    (∏ e ∈ (m.disjSum n).disjSum b, (bridgeGraph G H extL extR).weight e) =
      (∏ e ∈ m, G.weight e) * ∏ f ∈ n, H.weight f := by
  simp [Finset.prod_disjSum, bridgeGraph, disjointUnionGraph]

omit [Fintype V] [Fintype W] in
/-- Weighted bridge gluing is also valid after deleting vertices away from
the bridge endpoints. -/
theorem weightedPerfectMatch_bridge_active (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextL : Function.Injective extL) (hextR : Function.Injective extR)
    (activeG : Finset V) (activeH : Finset W)
    (hactiveL : ∀ i, extL i ∈ activeG) (hactiveR : ∀ i, extR i ∈ activeH) :
    weightedPerfectMatch (bridgeGraph G H extL extR) (activeG.disjSum activeH) =
      ∑ b : Finset B, weightedPerfectMatch G (activeG \ b.image extL) *
        weightedPerfectMatch H (activeH \ b.image extR) := by
  classical
  unfold weightedPerfectMatch
  rw [sum_finset_disjSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [sum_finset_disjSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [matchesExactly_bridge_active_iff G H extL extR hextL hextR
    activeG activeH hactiveL hactiveR, matchingWeight_bridge]
  split_ifs <;> simp_all

/-- The weighted bridge-gluing identity, indexed by the actual bridge edge set. -/
theorem weightedPerfectMatch_bridge (G : WeightedGraph V E K)
    (H : WeightedGraph W F K) (extL : B → V) (extR : B → W)
    (hextL : Function.Injective extL) (hextR : Function.Injective extR) :
    weightedPerfectMatch (bridgeGraph G H extL extR) Finset.univ =
      ∑ b : Finset B, weightedPerfectMatch G (bridgeRemaining extL b) *
        weightedPerfectMatch H (bridgeRemaining extR b) := by
  classical
  unfold weightedPerfectMatch
  rw [sum_finset_disjSum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [sum_finset_disjSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [matchesExactly_bridge_iff G H extL extR hextL hextR, matchingWeight_bridge]
  split_ifs <;> simp_all

/-- A Boolean boundary assignment is equivalently a selected set of bridges. -/
def bridgeBitsEquiv (B : Type*) [Fintype B] : (B → Bool) ≃ Finset B where
  toFun x := Finset.univ.filter (fun b => x b = true)
  invFun b := fun i => decide (i ∈ b)
  left_inv x := by
    funext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    cases x i <;> rfl
  right_inv b := by
    ext i
    simp

/-- The bit value `true` deletes the endpoint covered by that bridge. -/
theorem bridgeRemaining_bits {s : ℕ} (ext : Fin s → V) (x : Fin s → Bool) :
    bridgeRemaining ext (bridgeBitsEquiv (Fin s) x) = deletionActive ext x := by
  classical
  ext v
  simp [bridgeRemaining, bridgeBitsEquiv, deletionActive]

/-- Actual graph gluing contracts matching signatures with the same deletion bit
at both ends. This is a graph-algebra theorem, not a planar closure assertion. -/
theorem weightedPerfectMatch_bridge_deletionSignature {s : ℕ}
    (G : WeightedGraph V E K) (H : WeightedGraph W F K)
    (extL : Fin s → V) (extR : Fin s → W)
    (hextL : Function.Injective extL) (hextR : Function.Injective extR) :
    weightedPerfectMatch (bridgeGraph G H extL extR) Finset.univ =
      ∑ x : Fin s → Bool, deletionSignature G extL x * deletionSignature H extR x := by
  rw [weightedPerfectMatch_bridge G H extL extR hextL hextR,
    ← (bridgeBitsEquiv (Fin s)).sum_comp]
  simp only [bridgeRemaining_bits, deletionSignature]

end
end MatchgateWidth
