import MatchgateWidth.MatchingOverlayPath
import MatchgateWidth.SubsetSignParity

/-!
# Boundary cancellation for actual weighted matching signatures

This file separates finite matching combinatorics from the remaining topological
bridge. Its boundary hypothesis forbids two actual overlay endpoint paths from
joining alternating external vertices. It does not assume a matchgate identity,
a signed cancellation, or parity of boundary indices.
-/

namespace MatchgateWidth
noncomputable section
open Classical
open scoped symmDiff

/-- A fixed-point-free involution on a finite linearly ordered set pairs its
members, so its cardinality is even. -/
theorem even_card_of_pairing {α : Type*} [LinearOrder α] (S : Finset α)
    (f : α → α) (hmem : ∀ i ∈ S, f i ∈ S)
    (hinv : ∀ i ∈ S, f (f i) = i) (hne : ∀ i ∈ S, f i ≠ i) : Even S.card := by
  have hc : (S.filter fun i => i < f i).card = (S.filter fun i => ¬ i < f i).card := by
    apply Finset.card_bij (fun i _ => f i)
    · intro i hi
      obtain ⟨hi, hlt⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hmem i hi, by rw [hinv i hi]; exact not_lt_of_gt hlt⟩
    · intro i hi j hj he
      have hi' := (Finset.mem_filter.mp hi).1
      have hj' := (Finset.mem_filter.mp hj).1
      simpa [hinv i hi', hinv j hj'] using congrArg f he
    · intro j hj
      obtain ⟨hj, hlt⟩ := Finset.mem_filter.mp hj
      refine ⟨f j, Finset.mem_filter.mpr ⟨hmem j hj, ?_⟩, hinv j hj⟩
      rw [hinv j hj]
      exact lt_of_le_of_ne (le_of_not_gt hlt) (hne j hj)
  have hs := Finset.card_filter_add_card_filter_not (s := S) (fun i => i < f i)
  exact ⟨(S.filter fun i => i < f i).card, by omega⟩

/-- Noncrossing means no two pairs have alternating endpoints in the linear
boundary order. The cyclic wrap is represented by nesting around the marked cut. -/
def NoncrossingPairing {s : ℕ} (D : Finset (Fin s)) (f : Fin s → Fin s) : Prop :=
  ∀ i ∈ D, ∀ j ∈ D, ¬ (i < j ∧ j < f i ∧ f i < f j)

/-- The interior of each noncrossing pair is closed under its perfect pairing. -/
theorem noncrossing_pairing_interval_closed {s : ℕ} (D : Finset (Fin s))
    (f : Fin s → Fin s) (hmem : ∀ i ∈ D, f i ∈ D)
    (hinv : ∀ i ∈ D, f (f i) = i) (_hne : ∀ i ∈ D, f i ≠ i)
    (hnc : NoncrossingPairing D f) {i j : Fin s} (hi : i ∈ D) (hj : j ∈ D)
    (hij : i < j) (hji : j < f i) : i < f j ∧ f j < f i := by
  have hfi : f j ≠ i := by
    intro he
    have := hinv j hj
    rw [he] at this
    exact (ne_of_lt hji) this.symm
  have hfj : f j ≠ f i := by
    intro he
    have he' := congrArg f he
    rw [hinv j hj, hinv i hi] at he'
    exact (ne_of_lt hij) he'.symm
  have hlo : i < f j := by
    by_contra h
    have hfji : f j < i := lt_of_le_of_ne (le_of_not_gt h) hfi
    exact hnc (f j) (hmem j hj) i hi ⟨hfji, by simpa [hinv j hj] using hij,
      by simpa [hinv j hj] using hji⟩
  have hhi : f j < f i := by
    by_contra h
    exact hnc i hi j hj ⟨hij, hji, lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hfj)⟩
  exact ⟨hlo, hhi⟩

/-- Noncrossing forces an even number of discrepancy endpoints strictly between
paired endpoints. This is a derived combinatorial fact, not a geometric axiom. -/
theorem noncrossing_pairing_even_between {s : ℕ} (D : Finset (Fin s))
    (f : Fin s → Fin s) (hmem : ∀ i ∈ D, f i ∈ D)
    (hinv : ∀ i ∈ D, f (f i) = i) (hne : ∀ i ∈ D, f i ≠ i)
    (hnc : NoncrossingPairing D f) (i : Fin s) (hi : i ∈ D) :
    Even (D.filter fun j => i < j ∧ j < f i).card := by
  apply even_card_of_pairing _ f
  · intro j hj
    obtain ⟨hj, hlo, hhi⟩ := Finset.mem_filter.mp hj
    exact Finset.mem_filter.mpr ⟨hmem j hj,
      noncrossing_pairing_interval_closed D f hmem hinv hne hnc hi hj hlo hhi⟩
  · intro j hj; exact hinv j (Finset.mem_filter.mp hj).1
  · intro j hj; exact hne j (Finset.mem_filter.mp hj).1

/-- The sorted-position signs of paired discrepancy ports are opposite. -/
theorem noncrossing_pairing_sign {s : ℕ} {R : Type*} [CommRing R]
    (D : Finset (Fin s)) (f : Fin s → Fin s) (hmem : ∀ i ∈ D, f i ∈ D)
    (hinv : ∀ i ∈ D, f (f i) = i) (hne : ∀ i ∈ D, f i ≠ i)
    (hnc : NoncrossingPairing D f) (i : Fin s) (hi : i ∈ D) :
    (-1 : R) ^ subsetBelow D (f i) = -((-1 : R) ^ subsetBelow D i) := by
  have aux (i : Fin s) (hi : i ∈ D) (hlt : i < f i) :
      (-1 : R) ^ subsetBelow D (f i) = -((-1 : R) ^ subsetBelow D i) := by
    have hsplit : D.filter (· < f i) =
        insert i ((D.filter (· < i)) ∪ (D.filter fun j => i < j ∧ j < f i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_union]
      constructor
      · rintro ⟨hj, hjf⟩
        rcases lt_trichotomy j i with hjlt | rfl | hjgt
        · exact Or.inr (Or.inl ⟨hj, hjlt⟩)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr ⟨hj, hjgt, hjf⟩)
      · rintro (rfl | ⟨hj, hjlt⟩ | ⟨hj, hjgt, hjf⟩)
        · exact ⟨hi, hlt⟩
        · exact ⟨hj, hjlt.trans hlt⟩
        · exact ⟨hj, hjf⟩
    have hd : Disjoint (D.filter (· < i)) (D.filter fun j => i < j ∧ j < f i) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      exact (not_lt_of_gt (Finset.mem_filter.mp hj).2) (Finset.mem_filter.mp hk).2.1
    have hni : i ∉ (D.filter (· < i)) ∪ (D.filter fun j => i < j ∧ j < f i) := by simp
    unfold subsetBelow
    rw [hsplit, Finset.card_insert_of_notMem hni, Finset.card_union_of_disjoint hd,
      pow_succ, pow_add, (noncrossing_pairing_even_between D f hmem hinv hne hnc i hi).neg_one_pow]
    simp
  rcases lt_or_gt_of_ne (Ne.symm (hne i hi)) with hlt | hgt
  · exact aux i hi hlt
  · have h := aux (f i) (hmem i hi) (by simpa [hinv i hi] using hgt)
    rw [hinv i hi] at h
    rw [h, neg_neg]

namespace SimpleEdgePath
variable {V E K : Type*} {G : WeightedGraph V E K} {r : ℕ}

/-- Reverse an actual edge-identity path. -/
def reverse (q : SimpleEdgePath G r) : SimpleEdgePath G r where
  vertex := fun i => q.vertex i.rev
  edge := fun i => q.edge i.rev
  vertex_injective := q.vertex_injective.comp Fin.rev_injective
  edge_injective := q.edge_injective.comp Fin.rev_injective
  incidence := by
    intro i
    simpa only [Fin.rev_castSucc, Fin.rev_succ, or_comm] using q.incidence i.rev

@[simp] theorem reverse_start (q : SimpleEdgePath G r) :
    q.reverse.vertex 0 = q.vertex (Fin.last (r + 1)) := by simp [reverse]
@[simp] theorem reverse_end (q : SimpleEdgePath G r) :
    q.reverse.vertex (Fin.last (r + 1)) = q.vertex 0 := by simp [reverse]
@[simp] theorem reverse_edgeSet (q : SimpleEdgePath G r) : q.reverse.edgeSet = q.edgeSet := by
  ext e
  simp only [edgeSet, Finset.mem_image, Finset.mem_univ, true_and, reverse]
  constructor <;> rintro ⟨i, hi⟩
  · exact ⟨i.rev, hi⟩
  · exact ⟨i.rev, by simpa using hi⟩
end SimpleEdgePath

/-- An overlay endpoint path can be traversed from its opposite endpoint. -/
theorem IsOverlayEndpointPath.reverse {V E K : Type*} {G : WeightedGraph V E K}
    {m n : Finset E} {a b : V} {p : Finset E}
    (h : IsOverlayEndpointPath G m n a (b, p)) : IsOverlayEndpointPath G m n b (a, p) := by
  obtain ⟨r, q, hs, he, hp, hqe, hqend⟩ := h
  refine ⟨r, q.reverse, by simpa using he, by simpa using hs, by simpa using hp, ?_, ?_⟩
  · intro i; exact hqe i.rev
  · intro v hv
    apply hqend v
    simpa only [SimpleEdgePath.reverse_start, SimpleEdgePath.reverse_end, or_comm] using hv

/-- Reversing the unique endpoint path changes only its first endpoint. -/
theorem overlayEndpointPath_mate {V E K : Type*} (G : WeightedGraph V E K)
    (m n : Finset E) (hm : ∀ v, matchingDegree G m v ≤ 1)
    (hn : ∀ v, matchingDegree G n v ≤ 1) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    overlayEndpointPath G m n (overlayEndpointPath G m n a).1 =
      (a, (overlayEndpointPath G m n a).2) := by
  have hp := overlayEndpointPath_spec G m n hm hn a ha
  have hr := hp.reverse
  have hex := overlayEndpointPath_spec_of_exists G m n _ ⟨_, hr⟩
  exact hex.unique hm hn hr


/-- The sole geometric hypothesis: degree-at-most-one matching overlays have no
endpoint paths joining alternating boundary indices. This is a topological
consequence expected of disk drawings, not proved or assumed in their definition. -/
def BoundaryPathNoncrossing {V E K : Type*} {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) : Prop :=
  ∀ (m n : Finset E), (∀ v, matchingDegree G m v ≤ 1) →
    (∀ v, matchingDegree G n v ≤ 1) →
    ∀ (a b c d : Fin s) (p q : Finset E),
      IsOverlayEndpointPath G m n (ext a) (ext c, p) →
      IsOverlayEndpointPath G m n (ext b) (ext d, q) →
      a < b → b < c → c < d → False

/-- All degree-one vertices of this overlay are precisely its discrepancy ports. -/
structure BoundaryOverlay {V E K : Type*} {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (D : Finset (Fin s))
    (m n : Finset E) : Prop where
  first : ∀ v, matchingDegree G m v ≤ 1
  second : ∀ v, matchingDegree G n v ≤ 1
  endpoints : ∀ v, matchingDegree G m v + matchingDegree G n v = 1 ↔
    ∃ i ∈ D, ext i = v

/-- The boundary index of the actual opposite endpoint, with an unused fallback. -/
def boundaryMate {V E K : Type*} {s : ℕ} (G : WeightedGraph V E K)
    (ext : Fin s → V) (D : Finset (Fin s)) (m n : Finset E) (i : Fin s) : Fin s :=
  if h : ∃ j ∈ D, ext j = (overlayEndpointPath G m n (ext i)).1 then
    Classical.choose h else i

namespace BoundaryOverlay
variable {V E K : Type*} {s : ℕ} {G : WeightedGraph V E K}
  {ext : Fin s → V} {D : Finset (Fin s)} {m n : Finset E}

 theorem endpoint (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    matchingDegree G m (ext i) + matchingDegree G n (ext i) = 1 :=
  (h.endpoints _).mpr ⟨i, hi, rfl⟩

 theorem path (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    IsOverlayEndpointPath G m n (ext i) (overlayEndpointPath G m n (ext i)) :=
  overlayEndpointPath_spec G m n h.first h.second _ (h.endpoint hi)

 theorem mate_spec (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    boundaryMate G ext D m n i ∈ D ∧
      ext (boundaryMate G ext D m n i) = (overlayEndpointPath G m n (ext i)).1 := by
  have he := (h.path hi).certificate.overlay_endpoint_degree _ (Or.inr rfl)
  have hex := (h.endpoints _).mp he
  unfold boundaryMate
  rw [dite_eq_left hex]
  exact Classical.choose_spec hex

 theorem mate_mem (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    boundaryMate G ext D m n i ∈ D := (h.mate_spec hi).1

 theorem mate_ext (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    ext (boundaryMate G ext D m n i) = (overlayEndpointPath G m n (ext i)).1 :=
  (h.mate_spec hi).2

 theorem mate_ne (h : BoundaryOverlay G ext D m n) {i : Fin s} (hi : i ∈ D) :
    boundaryMate G ext D m n i ≠ i := by
  intro he
  have hc := (h.path hi).certificate.distinct
  rw [← h.mate_ext hi, he] at hc
  exact hc rfl

 theorem mate_involutive (h : BoundaryOverlay G ext D m n) (hext : Function.Injective ext)
    {i : Fin s} (hi : i ∈ D) :
    boundaryMate G ext D m n (boundaryMate G ext D m n i) = i := by
  apply hext
  rw [h.mate_ext (h.mate_mem hi), h.mate_ext hi,
    overlayEndpointPath_mate G m n h.first h.second _ (h.endpoint hi)]

 theorem mate_noncrossing (h : BoundaryOverlay G ext D m n)
    (hnc : BoundaryPathNoncrossing G ext) :
    NoncrossingPairing D (boundaryMate G ext D m n) := by
  intro i hi j hj hij
  have hp := h.path hi
  have hq := h.path hj
  have hp' : IsOverlayEndpointPath G m n (ext i)
      (ext (boundaryMate G ext D m n i), (overlayEndpointPath G m n (ext i)).2) := by
    simpa only [h.mate_ext hi] using hp
  have hq' : IsOverlayEndpointPath G m n (ext j)
      (ext (boundaryMate G ext D m n j), (overlayEndpointPath G m n (ext j)).2) := by
    simpa only [h.mate_ext hj] using hq
  exact hnc m n h.first h.second _ _ _ _ _ _ hp' hq' hij.1 hij.2.1 hij.2.2

 theorem mate_sign {R : Type*} [CommRing R] (h : BoundaryOverlay G ext D m n)
    (hext : Function.Injective ext) (hnc : BoundaryPathNoncrossing G ext)
    {i : Fin s} (hi : i ∈ D) :
    (-1 : R) ^ subsetBelow D (boundaryMate G ext D m n i) =
      -((-1 : R) ^ subsetBelow D i) :=
  noncrossing_pairing_sign D _ (fun _ => h.mate_mem)
    (fun _ => h.mate_involutive hext) (fun _ => h.mate_ne) (h.mate_noncrossing hnc) i hi

 theorem switched (h : BoundaryOverlay G ext D m n) (p : Finset E)
    {i : Fin s} (hi : i ∈ D) (hp : p = (overlayEndpointPath G m n (ext i)).2) :
    BoundaryOverlay G ext D (switchEdges m n p) (switchEdges n m p) where
  first := by
    rw [hp]
    exact (h.path hi).certificate.degree_le_one_switched h.first h.second
  second := by
    rw [hp]
    exact (h.path hi).certificate.symm.degree_le_one_switched h.second h.first
  endpoints := by intro v; rw [matchingDegree_switchEdges_add]; exact h.endpoints v

 theorem mate_switch (h : BoundaryOverlay G ext D m n) (p : Finset E)
    {i : Fin s} (hi : i ∈ D) :
    boundaryMate G ext D (switchEdges m n p) (switchEdges n m p) i =
      boundaryMate G ext D m n i := by
  unfold boundaryMate
  rw [overlayEndpointPath_switch G m n p h.first h.second _ (h.endpoint hi)]
end BoundaryOverlay

/-- Switching an endpoint path, then switching it from its other endpoint, is
the identity on the actual two matching edge sets. -/
theorem endpointMatchingSwitch_mate_involutive {V E K : Type*} (G : WeightedGraph V E K)
    (m n : Finset E) (hm : ∀ v, matchingDegree G m v ≤ 1)
    (hn : ∀ v, matchingDegree G n v ≤ 1) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    endpointMatchingSwitch G (overlayEndpointPath G m n a).1
      (endpointMatchingSwitch G a (m, n)) = (m, n) := by
  have hb := (overlayEndpointPath_spec G m n hm hn a ha).certificate.overlay_endpoint_degree
    (overlayEndpointPath G m n a).1 (Or.inr rfl)
  dsimp only [endpointMatchingSwitch]
  rw [overlayEndpointPath_switch G m n _ hm hn _ hb,
    overlayEndpointPath_mate G m n hm hn a ha]
  simp only [switchEdges_involutive]


private theorem symmDiff_common_singleton {V : Type*} (A B : Finset V) (a : V) :
    (A ∆ {a}) ∆ (B ∆ {a}) = A ∆ B := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_singleton]
  tauto

private theorem symmDiff_singleton_pair {V : Type*} (A : Finset V) {a b : V}
    (hab : a ≠ b) : (A ∆ {a}) ∆ {a, b} = A ∆ {b} := by
  ext v
  simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
  grind

/-- A genuine summand consists of a discrepancy index and two actual matchings. -/
def IsBoundaryMatchingTerm {V E K : Type*} {s : ℕ} (G : WeightedGraph V E K)
    (ext : Fin s → V) (A B : Finset V) (D : Finset (Fin s))
    (x : Fin s × (Finset E × Finset E)) : Prop :=
  x.1 ∈ D ∧ MatchesExactly G (A ∆ {ext x.1}) x.2.1 ∧
    MatchesExactly G (B ∆ {ext x.1}) x.2.2

namespace IsBoundaryMatchingTerm
variable {V E K : Type*} {s : ℕ} {G : WeightedGraph V E K}
  {ext : Fin s → V} {A B : Finset V} {D : Finset (Fin s)}
  {x : Fin s × (Finset E × Finset E)}

 theorem overlay (h : IsBoundaryMatchingTerm G ext A B D x)
    (hD : A ∆ B = D.image ext) : BoundaryOverlay G ext D x.2.1 x.2.2 where
  first := by intro v; rw [h.2.1 v]; split_ifs <;> omega
  second := by intro v; rw [h.2.2 v]; split_ifs <;> omega
  endpoints := by
    intro v
    rw [matchesExactly_overlay_endpoint_iff G h.2.1 h.2.2 v,
      symmDiff_common_singleton, hD]
    exact Finset.mem_image
end IsBoundaryMatchingTerm

/-- The combinatorially constructed switch on actual MGI summands. -/
def boundaryMatchingTermSwitch {V E K : Type*} {s : ℕ} (G : WeightedGraph V E K)
    (ext : Fin s → V) (D : Finset (Fin s))
    (x : Fin s × (Finset E × Finset E)) : Fin s × (Finset E × Finset E) :=
  (boundaryMate G ext D x.2.1 x.2.2 x.1, endpointMatchingSwitch G (ext x.1) x.2)

namespace IsBoundaryMatchingTerm
variable {V E K : Type*} {s : ℕ} {G : WeightedGraph V E K}
  {ext : Fin s → V} {A B : Finset V} {D : Finset (Fin s)}
  {x : Fin s × (Finset E × Finset E)}

 theorem switched (h : IsBoundaryMatchingTerm G ext A B D x)
    (hD : A ∆ B = D.image ext) :
    IsBoundaryMatchingTerm G ext A B D (boundaryMatchingTermSwitch G ext D x) := by
  have ho := h.overlay hD
  have hp := endpointMatchingSwitch_matchesExactly G h.2.1 h.2.2 (ext x.1) (ho.endpoint h.1)
  have hn := (ho.path h.1).certificate.distinct
  rw [symmDiff_singleton_pair _ hn, symmDiff_singleton_pair _ hn, ← ho.mate_ext h.1] at hp
  exact ⟨ho.mate_mem h.1, hp⟩

 theorem switch_involutive (h : IsBoundaryMatchingTerm G ext A B D x)
    (hD : A ∆ B = D.image ext) (hext : Function.Injective ext) :
    boundaryMatchingTermSwitch G ext D (boundaryMatchingTermSwitch G ext D x) = x := by
  have ho := h.overlay hD
  apply Prod.ext
  · change boundaryMate G ext D
      (switchEdges x.2.1 x.2.2 (overlayEndpointPath G x.2.1 x.2.2 (ext x.1)).2)
      (switchEdges x.2.2 x.2.1 (overlayEndpointPath G x.2.1 x.2.2 (ext x.1)).2)
      (boundaryMate G ext D x.2.1 x.2.2 x.1) = x.1
    rw [ho.mate_switch _ (ho.mate_mem h.1), ho.mate_involutive hext h.1]
  · change endpointMatchingSwitch G (ext (boundaryMate G ext D x.2.1 x.2.2 x.1))
      (endpointMatchingSwitch G (ext x.1) x.2) = x.2
    rw [ho.mate_ext h.1]
    exact endpointMatchingSwitch_mate_involutive G _ _ ho.first ho.second _ (ho.endpoint h.1)

 theorem switch_ne (h : IsBoundaryMatchingTerm G ext A B D x)
    (hD : A ∆ B = D.image ext) : boundaryMatchingTermSwitch G ext D x ≠ x := by
  intro he
  exact (h.overlay hD).mate_ne h.1 (congrArg Prod.fst he)
end IsBoundaryMatchingTerm

/-- Expand a product of matching sums into the actual matching-pair summands. -/
theorem weightedPerfectMatch_mul {V E K : Type*} [Fintype E] [CommSemiring K]
    (G : WeightedGraph V E K) (A B : Finset V) :
    weightedPerfectMatch G A * weightedPerfectMatch G B =
      ∑ mn : Finset E × Finset E, if MatchesExactly G A mn.1 ∧ MatchesExactly G B mn.2
        then (∏ e ∈ mn.1, G.weight e) * (∏ e ∈ mn.2, G.weight e) else 0 := by
  rw [Fintype.sum_prod_type]
  unfold weightedPerfectMatch
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hm : MatchesExactly G A m <;> by_cases hn : MatchesExactly G B n <;> simp [hm, hn]

/-- The signed sum of the actual matching-pair terms vanishes by the constructed
path switch. Zero weights, parallel edges, and arbitrary characteristic are allowed. -/
theorem boundary_matching_terms_sum_zero {V E K : Type*} [Fintype E] [CommRing K]
    {s : ℕ} (G : WeightedGraph V E K) (ext : Fin s → V)
    (hext : Function.Injective ext) (hnc : BoundaryPathNoncrossing G ext)
    (A B : Finset V) (D : Finset (Fin s)) (hD : A ∆ B = D.image ext) :
    (∑ x ∈ Finset.univ.filter (IsBoundaryMatchingTerm G ext A B D),
      (-1 : K) ^ subsetBelow D x.1 *
        ((∏ e ∈ x.2.1, G.weight e) * (∏ e ∈ x.2.2, G.weight e))) = 0 := by
  apply Finset.sum_involution (fun x _ => boundaryMatchingTermSwitch G ext D x)
  · intro x hx
    have ht := (Finset.mem_filter.mp hx).2
    have ho := ht.overlay hD
    change _ + (-1 : K) ^ subsetBelow D (boundaryMate G ext D x.2.1 x.2.2 x.1) *
      ((∏ e ∈ (endpointMatchingSwitch G (ext x.1) x.2).1, G.weight e) *
        (∏ e ∈ (endpointMatchingSwitch G (ext x.1) x.2).2, G.weight e)) = 0
    rw [ho.mate_sign hext hnc ht.1, endpointMatchingSwitch_weight]
    ring
  · intro x hx _
    exact (Finset.mem_filter.mp hx).2.switch_ne hD
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.switched hD⟩
  · intro x hx
    exact (Finset.mem_filter.mp hx).2.switch_involutive hD hext

/-- Actual weighted perfect-matching sums satisfy the boundary alternating
identity, with only the explicitly stated noncrossing-path hypothesis. -/
theorem weightedPerfectMatch_boundary_identity {V E K : Type*} [Fintype E] [CommRing K]
    {s : ℕ} (G : WeightedGraph V E K) (ext : Fin s → V)
    (hext : Function.Injective ext) (hnc : BoundaryPathNoncrossing G ext)
    (A B : Finset V) (D : Finset (Fin s)) (hD : A ∆ B = D.image ext) :
    (∑ i ∈ D, (-1 : K) ^ subsetBelow D i *
      weightedPerfectMatch G (A ∆ {ext i}) * weightedPerfectMatch G (B ∆ {ext i})) = 0 := by
  have hz := boundary_matching_terms_sum_zero G ext hext hnc A B D hD
  rw [Finset.sum_filter, Fintype.sum_prod_type] at hz
  have heq : (∑ i ∈ D, (-1 : K) ^ subsetBelow D i *
      weightedPerfectMatch G (A ∆ {ext i}) * weightedPerfectMatch G (B ∆ {ext i})) =
      ∑ i : Fin s, ∑ mn : Finset E × Finset E,
        if IsBoundaryMatchingTerm G ext A B D (i, mn) then
          (-1 : K) ^ subsetBelow D i *
            ((∏ e ∈ mn.1, G.weight e) * (∏ e ∈ mn.2, G.weight e)) else 0 := by
    have hd : Finset.univ.filter (fun i : Fin s => i ∈ D) = D := by ext i; simp
    conv_lhs =>
      arg 1
      rw [← hd]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ D
    · simp only [hi, ite_true, IsBoundaryMatchingTerm, true_and]
      rw [mul_assoc, weightedPerfectMatch_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mn _
      split_ifs <;> simp
    · simp [hi, IsBoundaryMatchingTerm]
  rw [heq]
  exact hz


/-- Subset coordinates for the actual weighted deletion signature. A selected
port is deleted, exactly as in `deletionSignature`. -/
def deletionSubsetSignature {V E K : Type*} [Fintype V] [Fintype E] [CommSemiring K]
    {s : ℕ} (G : WeightedGraph V E K) (ext : Fin s → V) : SubsetSignature s K :=
  fun S => weightedPerfectMatch G (S.image ext)ᶜ

/-- The subset-coordinate definition agrees with the original Boolean deletion
semantics, without any assumptions on the graph or external enumeration. -/
theorem deletionSubsetSignature_eq_deletionSignature {V E K : Type*}
    [Fintype V] [Fintype E] [CommSemiring K] {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (S : Finset (Fin s)) :
    deletionSubsetSignature G ext S = deletionSignature G ext (fun i => decide (i ∈ S)) := by
  unfold deletionSubsetSignature deletionSignature
  congr 1
  ext v
  simp [deletionActive, Finset.mem_image]

/-- Toggling a deletion bit toggles the corresponding active external vertex. -/
theorem deletionSubsetActive_toggle {V : Type*} [Fintype V] {s : ℕ}
    (ext : Fin s → V) (hext : Function.Injective ext) (S : Finset (Fin s)) (i : Fin s) :
    ((S ∆ {i}).image ext)ᶜ = (S.image ext)ᶜ ∆ {ext i} := by
  rw [Finset.image_symmDiff _ _ hext, Finset.image_singleton]
  ext v
  simp only [Finset.mem_compl, Finset.mem_symmDiff]
  tauto

/-- Complementary deletion sets have exactly the advertised discrepancy ports. -/
theorem deletionSubsetActive_discrepancy {V : Type*} [Fintype V] {s : ℕ}
    (ext : Fin s → V) (hext : Function.Injective ext) (A B : Finset (Fin s)) :
    (A.image ext)ᶜ ∆ (B.image ext)ᶜ = (A ∆ B).image ext := by
  rw [Finset.image_symmDiff _ _ hext]
  ext v
  simp only [Finset.mem_compl, Finset.mem_symmDiff]
  tauto

/-- The actual weighted deletion signature satisfies all matchgate identities
provided its actual overlay endpoint paths satisfy the stated boundary
noncrossing property. No topology-to-noncrossing bridge is claimed here. -/
theorem deletionSubsetSignature_matchgateIdentities {V E K : Type*}
    [Fintype V] [Fintype E] [CommRing K] {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (hext : Function.Injective ext)
    (hnc : BoundaryPathNoncrossing G ext) :
    MatchgateIdentities (deletionSubsetSignature G ext) := by
  intro A B
  rw [matchgateSum_eq_neg_sum]
  have hz := weightedPerfectMatch_boundary_identity G ext hext hnc
    (A.image ext)ᶜ (B.image ext)ᶜ (A ∆ B)
    (deletionSubsetActive_discrepancy ext hext A B)
  have heq : (∑ i ∈ A ∆ B, (-1 : K) ^ subsetBelow (A ∆ B) i *
      deletionSubsetSignature G ext (A ∆ {i}) *
      deletionSubsetSignature G ext (B ∆ {i})) = 0 := by
    simpa only [deletionSubsetSignature, deletionSubsetActive_toggle ext hext] using hz
  rw [heq, neg_zero]


/-- Direct formulation for the original Boolean deletion signature. -/
theorem deletionSignature_matchgateIdentities {V E K : Type*}
    [Fintype V] [Fintype E] [CommRing K] {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (hext : Function.Injective ext)
    (hnc : BoundaryPathNoncrossing G ext) :
    MatchgateIdentities (fun S => deletionSignature G ext (fun i => decide (i ∈ S))) := by
  have heq : (fun S => deletionSignature G ext (fun i => decide (i ∈ S))) =
      deletionSubsetSignature G ext := by
    funext S
    exact (deletionSubsetSignature_eq_deletionSignature G ext S).symm
  rw [heq]
  exact deletionSubsetSignature_matchgateIdentities G ext hext hnc

/-- The actual MGI-summand switch packaged as a fixed-point-free equivalence.
Its domain contains matching edge sets, rather than assumed signature values. -/
def boundaryMatchingTermInvolution {V E K : Type*} {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (A B : Finset V)
    (D : Finset (Fin s)) (hD : A ∆ B = D.image ext) (hext : Function.Injective ext) :
    {x // IsBoundaryMatchingTerm G ext A B D x} ≃
      {x // IsBoundaryMatchingTerm G ext A B D x} where
  toFun x := ⟨boundaryMatchingTermSwitch G ext D x.val, x.property.switched hD⟩
  invFun x := ⟨boundaryMatchingTermSwitch G ext D x.val, x.property.switched hD⟩
  left_inv x := Subtype.ext (x.property.switch_involutive hD hext)
  right_inv x := Subtype.ext (x.property.switch_involutive hD hext)

/-- No MGI term is fixed by the packaged actual-matching switch. -/
theorem boundaryMatchingTermInvolution_ne {V E K : Type*} {s : ℕ}
    (G : WeightedGraph V E K) (ext : Fin s → V) (A B : Finset V)
    (D : Finset (Fin s)) (hD : A ∆ B = D.image ext) (hext : Function.Injective ext)
    (x : {x // IsBoundaryMatchingTerm G ext A B D x}) :
    boundaryMatchingTermInvolution G ext A B D hD hext x ≠ x := by
  intro he
  exact x.property.switch_ne hD (congrArg Subtype.val he)

end
end MatchgateWidth
