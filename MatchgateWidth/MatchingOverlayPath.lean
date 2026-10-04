import MatchgateWidth.MatchingSwitch

/-!
# Paths from degree-one matching-overlay endpoints

This module constructs a positive-length simple edge-identity path from an
endpoint of a finite overlay of two matchings. It uses finite edge-set induction,
not planarity. Parallel edges remain distinct and common matching edges are
excluded by the symmetric difference.

The opposite endpoint and path edge set are proved unique. Consequently the path
selected after switching is exactly the original selected path. This supplies
`endpointMatchingInvolution`, a fixed-point-free involutive equivalence of actual
matching pairs, together with endpoint active-set toggling and weight preservation.

No finite vertex enumeration or algebraic assumptions on graph weights are needed
for the construction. Weight-product preservation uses a commutative monoid.
Boundary noncrossing parity and the graph-signature MGI theorem are not asserted.
-/

namespace MatchgateWidth

noncomputable section
open Classical
open scoped symmDiff

variable {V E K : Type*}

/-- Taking an edge subset cannot increase incidence degree. -/
theorem matchingDegree_mono (G : WeightedGraph V E K) {m n : Finset E}
    (h : m ⊆ n) (v : V) : matchingDegree G m v ≤ matchingDegree G n v :=
  Finset.sum_le_sum_of_subset h

@[simp] theorem matchingDegree_singleton (G : WeightedGraph V E K) (e : E) (v : V) :
    matchingDegree G {e} v = (if G.left e = v then 1 else 0) +
      (if G.right e = v then 1 else 0) := by
  simp [matchingDegree]

theorem matchingDegree_pos_iff (G : WeightedGraph V E K) (m : Finset E) (v : V) :
    0 < matchingDegree G m v ↔ ∃ e ∈ m, G.left e = v ∨ G.right e = v := by
  unfold matchingDegree
  rw [Finset.sum_pos_iff]
  simp [Nat.pos_iff_ne_zero]

theorem matchingDegree_erase_add (G : WeightedGraph V E K) {m : Finset E}
    {e : E} (he : e ∈ m) (v : V) :
    matchingDegree G (m.erase e) v + matchingDegree G {e} v = matchingDegree G m v := by
  simpa only [matchingDegree, Finset.sum_singleton] using Finset.sum_erase_add m
    (fun f => (if G.left f = v then 1 else 0) + (if G.right f = v then 1 else 0)) he

/-- Erasing a symmetric-difference edge removes exactly one copy from the overlay. -/
theorem matchingDegree_erase_pair_add (G : WeightedGraph V E K) {m n : Finset E}
    {e : E} (he : e ∈ m ∆ n) (v : V) :
    matchingDegree G (m.erase e) v + matchingDegree G (n.erase e) v +
      matchingDegree G {e} v = matchingDegree G m v + matchingDegree G n v := by
  rcases Finset.mem_symmDiff.mp he with ⟨hm, hn⟩ | ⟨hn, hm⟩
  · rw [Finset.erase_eq_of_notMem hn]
    have h := matchingDegree_erase_add G hm v
    omega
  · rw [Finset.erase_eq_of_notMem hm]
    have h := matchingDegree_erase_add G hn v
    omega

/-- A degree-one overlay endpoint has an incident edge in its symmetric difference. -/
theorem exists_incident_symmDiff (G : WeightedGraph V E K) (m n : Finset E) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    ∃ e ∈ m ∆ n, G.left e = a ∨ G.right e = a := by
  have incident (s t : Finset E) (hs : 0 < matchingDegree G s a)
      (ht : matchingDegree G t a = 0) :
      ∃ e, e ∈ s ∧ e ∉ t ∧ (G.left e = a ∨ G.right e = a) := by
    obtain ⟨e, he, hi⟩ := (matchingDegree_pos_iff G s a).mp hs
    refine ⟨e, he, ?_, hi⟩
    intro het
    have hd := matchingDegree_mono G (Finset.singleton_subset_iff.mpr het) a
    have hp : 0 < matchingDegree G {e} a :=
      (matchingDegree_pos_iff G {e} a).mpr ⟨e, Finset.mem_singleton_self _, hi⟩
    omega
  by_cases hm : 0 < matchingDegree G m a
  · obtain ⟨e, he, hn, hi⟩ := incident m n hm (by omega)
    exact ⟨e, Finset.mem_symmDiff.mpr (Or.inl ⟨he, hn⟩), hi⟩
  · obtain ⟨e, he, hn, hi⟩ := incident n m (by omega) (by omega)
    exact ⟨e, Finset.mem_symmDiff.mpr (Or.inr ⟨he, hn⟩), hi⟩

namespace SimpleEdgePath

variable {G : WeightedGraph V E K} {r : ℕ}

/-- Every vertex of a positive-length simple path has positive path degree. -/
theorem degree_pos_of_mem (q : SimpleEdgePath G r) {v : V} (hv : v ∈ q.vertexSet) :
    0 < matchingDegree G q.edgeSet v := by
  have hd := q.degree_add_endpoints v
  have hn := q.endpoints_distinct
  rw [ite_eq_left hv] at hd
  split_ifs at hd <;> simp_all

/-- A path inside a zero-degree overlay cannot visit that vertex. -/
theorem vertex_not_mem_of_overlay_degree_zero (q : SimpleEdgePath G r)
    {m n : Finset E} (he : ∀ i, q.edge i ∈ m ∆ n) {v : V}
    (hv : matchingDegree G m v + matchingDegree G n v = 0) : v ∉ q.vertexSet := by
  intro hmem
  have hp := q.degree_pos_of_mem hmem
  have hs : q.edgeSet ⊆ m ∆ n := by
    intro e hm
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
    exact he i
  have hd := matchingDegree_eq_inter_add_inter G m n q.edgeSet hs v
  have hm := matchingDegree_mono G (Finset.inter_subset_left (s₁ := m) (s₂ := q.edgeSet)) v
  have hn := matchingDegree_mono G (Finset.inter_subset_left (s₁ := n) (s₂ := q.edgeSet)) v
  omega

/-- A single edge with either orientation is a simple positive-length path. -/
def single (e : E) (a b : V)
    (hi : (G.left e = a ∧ G.right e = b) ∨ (G.left e = b ∧ G.right e = a)) :
    SimpleEdgePath G 0 where
  vertex := ![a, b]
  edge := fun _ => e
  vertex_injective := by
    have hab : a ≠ b := by
      rcases hi with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> intro hab <;>
        apply G.loopless e <;> simp_all
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  edge_injective := by intro i j _; fin_cases i; fin_cases j; rfl
  incidence := by intro i; fin_cases i; simpa using hi

/-- Prepend a fresh vertex and edge to a simple edge-identity path. -/
def prepend (q : SimpleEdgePath G r) (a : V) (e : E)
    (ha : a ∉ q.vertexSet) (he : e ∉ q.edgeSet)
    (hi : (G.left e = a ∧ G.right e = q.vertex 0) ∨
      (G.left e = q.vertex 0 ∧ G.right e = a)) : SimpleEdgePath G (r + 1) where
  vertex := Fin.cases a q.vertex
  edge := Fin.cases e q.edge
  vertex_injective := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hij
        exact (ha (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij.symm⟩)).elim
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hij
        exact (ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hij⟩)).elim
      | succ j =>
        simp only [Fin.cases_succ] at hij
        exact congrArg Fin.succ (q.vertex_injective hij)
  edge_injective := by
    intro i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => rfl
      | succ j =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hij
        exact (he (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hij.symm⟩)).elim
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simp only [Fin.cases_zero, Fin.cases_succ] at hij
        exact (he (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hij⟩)).elim
      | succ j =>
        simp only [Fin.cases_succ] at hij
        exact congrArg Fin.succ (q.edge_injective hij)
  incidence := by
    intro i
    cases i using Fin.cases with
    | zero =>
      change (G.left e = a ∧ G.right e = q.vertex 0) ∨
        (G.left e = q.vertex 0 ∧ G.right e = a)
      exact hi
    | succ i => simpa [Fin.castSucc_succ] using q.incidence i

@[simp] theorem prepend_start (q : SimpleEdgePath G r) (a : V) (e : E)
    (ha : a ∉ q.vertexSet) (he : e ∉ q.edgeSet)
    (hi : (G.left e = a ∧ G.right e = q.vertex 0) ∨
      (G.left e = q.vertex 0 ∧ G.right e = a)) :
    (q.prepend a e ha he hi).vertex 0 = a := rfl

@[simp] theorem prepend_end (q : SimpleEdgePath G r) (a : V) (e : E)
    (ha : a ∉ q.vertexSet) (he : e ∉ q.edgeSet)
    (hi : (G.left e = a ∧ G.right e = q.vertex 0) ∨
      (G.left e = q.vertex 0 ∧ G.right e = a)) :
    (q.prepend a e ha he hi).vertex (Fin.last (r + 1 + 1)) = q.vertex (Fin.last (r + 1)) := by
  change (Fin.cases a q.vertex : Fin (r + 3) → V) (Fin.last (r + 2)) = _
  rw [← Fin.succ_last]
  rfl

end SimpleEdgePath

/-- Incidence of an edge described by its two distinct endpoints. -/
theorem matchingDegree_singleton_of_endpoints (G : WeightedGraph V E K)
    (e : E) (a c : V) (hac : a ≠ c)
    (hi : (G.left e = a ∧ G.right e = c) ∨ (G.left e = c ∧ G.right e = a))
    (v : V) : matchingDegree G {e} v = if v = a ∨ v = c then 1 else 0 := by
  rcases hi with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    by_cases h₁ : v = a <;> by_cases h₂ : v = c <;>
    simp_all [matchingDegree_singleton, eq_comm]

/-- A degree-one endpoint in two finite degree-at-most-one edge families lies on
an actual positive-length simple path to a different degree-one endpoint. The path
uses only symmetric-difference edges, so common edges are never traversed.

The proof removes the unique first edge and inducts on the total number of selected
edge identities. It works for arbitrary loopless finite-edge multigraphs. -/
theorem exists_simpleEdgePath_from_overlay_endpoint (G : WeightedGraph V E K)
    (m n : Finset E) (hm : ∀ v, matchingDegree G m v ≤ 1)
    (hn : ∀ v, matchingDegree G n v ≤ 1) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    ∃ (r : ℕ) (q : SimpleEdgePath G r), q.vertex 0 = a ∧
      (∀ i, q.edge i ∈ m ∆ n) ∧
      matchingDegree G m (q.vertex (Fin.last (r + 1))) +
        matchingDegree G n (q.vertex (Fin.last (r + 1))) = 1 := by
  have aux : ∀ k : ℕ, ∀ (m n : Finset E), m.card + n.card = k →
      (∀ v, matchingDegree G m v ≤ 1) → (∀ v, matchingDegree G n v ≤ 1) →
      ∀ a, matchingDegree G m a + matchingDegree G n a = 1 →
      ∃ (r : ℕ) (q : SimpleEdgePath G r), q.vertex 0 = a ∧
        (∀ i, q.edge i ∈ m ∆ n) ∧
        matchingDegree G m (q.vertex (Fin.last (r + 1))) +
          matchingDegree G n (q.vertex (Fin.last (r + 1))) = 1 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro m n hcard hm hn a ha
      obtain ⟨e, he, hi⟩ := exists_incident_symmDiff G m n a ha
      obtain ⟨c, hac, hie⟩ : ∃ c, a ≠ c ∧
          ((G.left e = a ∧ G.right e = c) ∨ (G.left e = c ∧ G.right e = a)) := by
        rcases hi with hl | hr
        · exact ⟨G.right e, by simpa [hl] using G.loopless e, Or.inl ⟨hl, rfl⟩⟩
        · exact ⟨G.left e, by simpa [hr] using Ne.symm (G.loopless e), Or.inr ⟨rfl, hr⟩⟩
      have hsingle := matchingDegree_singleton_of_endpoints G e a c hac hie
      have hma (v : V) : matchingDegree G (m.erase e) v ≤ 1 :=
        (matchingDegree_mono G (Finset.erase_subset e m) v).trans (hm v)
      have hna (v : V) : matchingDegree G (n.erase e) v ≤ 1 :=
        (matchingDegree_mono G (Finset.erase_subset e n) v).trans (hn v)
      have hremove := matchingDegree_erase_pair_add G he
      have hzeroA : matchingDegree G (m.erase e) a + matchingDegree G (n.erase e) a = 0 := by
        have hd := hremove a
        rw [hsingle, ite_eq_left (Or.inl rfl)] at hd
        omega
      have hC : matchingDegree G (m.erase e) c + matchingDegree G (n.erase e) c ≤ 1 := by
        have hd := hremove c
        rw [hsingle, ite_eq_left (Or.inr rfl)] at hd
        have hm' := hm c
        have hn' := hn c
        omega
      by_cases hzeroC : matchingDegree G (m.erase e) c + matchingDegree G (n.erase e) c = 0
      · refine ⟨0, SimpleEdgePath.single e a c hie, rfl, ?_, ?_⟩
        · intro i
          exact he
        · change matchingDegree G m c + matchingDegree G n c = 1
          have hd := hremove c
          rw [hsingle, ite_eq_left (Or.inr rfl)] at hd
          omega
      · have hlt : (m.erase e).card + (n.erase e).card < k := by
          have hm' := Finset.card_erase_le (s := m) (a := e)
          have hn' := Finset.card_erase_le (s := n) (a := e)
          rcases Finset.mem_symmDiff.mp he with ⟨hem, _⟩ | ⟨hen, _⟩
          · have hlt := Finset.card_erase_lt_of_mem hem
            omega
          · have hlt := Finset.card_erase_lt_of_mem hen
            omega
        obtain ⟨r, q, hstart, hqe, hend⟩ :=
          ih _ hlt (m.erase e) (n.erase e) rfl hma hna c (by omega)
        have hsub : (m.erase e) ∆ (n.erase e) ⊆ m ∆ n := by
          intro f hf
          simp only [Finset.mem_symmDiff, Finset.mem_erase] at hf ⊢
          tauto
        have hva : a ∉ q.vertexSet := q.vertex_not_mem_of_overlay_degree_zero hqe hzeroA
        have hea : e ∉ q.edgeSet := by
          intro heq
          obtain ⟨i, _, hieq⟩ := Finset.mem_image.mp heq
          have hi' := hqe i
          rw [hieq] at hi'
          simp only [Finset.mem_symmDiff, Finset.mem_erase, ne_eq, not_true_eq_false,
            false_and, not_false_eq_true, and_true, or_self] at hi'
        have hie' : (G.left e = a ∧ G.right e = q.vertex 0) ∨
            (G.left e = q.vertex 0 ∧ G.right e = a) := by rwa [hstart]
        refine ⟨r + 1, q.prepend a e hva hea hie', rfl, ?_, ?_⟩
        · intro i
          cases i using Fin.cases with
          | zero => exact he
          | succ i => exact hsub (hqe i)
        · rw [q.prepend_end]
          have hbA : q.vertex (Fin.last (r + 1)) ≠ a := by
            intro hb
            exact hva (Finset.mem_image.mpr ⟨Fin.last (r + 1), Finset.mem_univ _, hb⟩)
          have hbC : q.vertex (Fin.last (r + 1)) ≠ c := by
            rw [← hstart]
            exact Ne.symm q.endpoints_distinct
          have hd := hremove (q.vertex (Fin.last (r + 1)))
          rw [hsingle, ite_eq_right (by tauto)] at hd
          omega
  exact aux _ m n rfl hm hn a ha

/-- In particular, every degree-one endpoint of two actual matchings has a local
switch certificate. The two distinct endpoints are constructed rather than assumed. -/
theorem exists_alternatingPathEdges_from_endpoint (G : WeightedGraph V E K)
    {A B : Finset V} {m n : Finset E} (hm : MatchesExactly G A m)
    (hn : MatchesExactly G B n) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    ∃ (b : V) (p : Finset E), AlternatingPathEdges G m n p a b := by
  have hm' (v : V) : matchingDegree G m v ≤ 1 := by rw [hm v]; split_ifs <;> omega
  have hn' (v : V) : matchingDegree G n v ≤ 1 := by rw [hn v]; split_ifs <;> omega
  obtain ⟨r, q, hstart, hedges, hend⟩ :=
    exists_simpleEdgePath_from_overlay_endpoint G m n hm' hn' a ha
  refine ⟨q.vertex (Fin.last (r + 1)), q.edgeSet, ?_⟩
  have hc := q.alternatingPathEdges hedges (by
    intro v hv
    rcases hv with rfl | rfl
    · simpa [hstart] using ha
    · exact hend)
  simpa [hstart] using hc

/-- Incidence degree of an uncolored overlay subset is bounded by the sum of the
colored incidence degrees, with common edges counted in both colors on the right. -/
theorem matchingDegree_le_overlay (G : WeightedGraph V E K) {m n p : Finset E}
    (hp : p ⊆ m ∆ n) (v : V) :
    matchingDegree G p v ≤ matchingDegree G m v + matchingDegree G n v := by
  rw [matchingDegree_eq_inter_add_inter G m n p hp]
  exact add_le_add (matchingDegree_mono G Finset.inter_subset_left v)
    (matchingDegree_mono G Finset.inter_subset_left v)

namespace SimpleEdgePath

variable {G : WeightedGraph V E K} {r s : ℕ}

/-- Any vertex incident to a selected path edge belongs to the path. -/
theorem vertex_mem_of_incident_edge (q : SimpleEdgePath G r) {e : E}
    (he : e ∈ q.edgeSet) {v : V} (hi : G.left e = v ∨ G.right e = v) :
    v ∈ q.vertexSet := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
  rcases q.incidence i with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;>
    rcases hi with hv | hv
  · exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, hl.symm.trans hv⟩
  · exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, hr.symm.trans hv⟩
  · exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, hl.symm.trans hv⟩
  · exact Finset.mem_image.mpr ⟨i.castSucc, Finset.mem_univ _, hr.symm.trans hv⟩

/-- A path joining degree-one endpoints in a degree-at-most-two overlay uses all
incident overlay edges at every vertex it visits. This includes parallel edges. -/
theorem overlay_saturated (q : SimpleEdgePath G r) {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (hedges : ∀ i, q.edge i ∈ m ∆ n)
    (hendpoints : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    {v : V} (hv : v ∈ q.vertexSet) {e : E} (he : e ∈ m ∆ n)
    (hi : G.left e = v ∨ G.right e = v) : e ∈ q.edgeSet := by
  have hp : q.edgeSet ⊆ m ∆ n := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact hedges i
  have hcover : matchingDegree G m v + matchingDegree G n v ≤ matchingDegree G q.edgeSet v := by
    by_cases hend : v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1))
    · rw [hendpoints v hend, (q.alternatingPathEdges hedges hendpoints).endpoint_degree v hend]
    · have hd := q.degree_add_endpoints v
      have h₁ : q.vertex 0 ≠ v := by tauto
      have h₂ : q.vertex (Fin.last (r + 1)) ≠ v := by tauto
      simp only [h₁, h₂, ite_false, hv, ite_true, add_zero] at hd
      have hm' := hm v
      have hn' := hn v
      omega
  by_contra heq
  have hins := matchingDegree_le_overlay G (Finset.insert_subset he hp) v
  have hdeg : matchingDegree G (insert e q.edgeSet) v =
      matchingDegree G {e} v + matchingDegree G q.edgeSet v := by
    unfold matchingDegree
    rw [Finset.sum_insert heq, Finset.sum_singleton]
  have hpos : 0 < matchingDegree G {e} v :=
    (matchingDegree_pos_iff G {e} v).mpr ⟨e, Finset.mem_singleton_self _, hi⟩
  rw [hdeg] at hins
  omega

/-- Every path from the same start inside the overlay stays in its endpoint path. -/
theorem edges_subset_of_same_start (q : SimpleEdgePath G r) (q' : SimpleEdgePath G s)
    {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (he : ∀ i, q.edge i ∈ m ∆ n) (he' : ∀ i, q'.edge i ∈ m ∆ n)
    (hend : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    (hstart : q'.vertex 0 = q.vertex 0) : q'.edgeSet ⊆ q.edgeSet := by
  have hv : ∀ i, q'.vertex i ∈ q.vertexSet := by
    intro i
    induction i using Fin.induction with
    | zero =>
      rw [hstart]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
    | succ i ih =>
      have hleft : G.left (q'.edge i) = q'.vertex i.castSucc ∨
          G.right (q'.edge i) = q'.vertex i.castSucc := by
        rcases q'.incidence i with ⟨hl, _⟩ | ⟨_, hr⟩
        · exact Or.inl hl
        · exact Or.inr hr
      have hright : G.left (q'.edge i) = q'.vertex i.succ ∨
          G.right (q'.edge i) = q'.vertex i.succ := by
        rcases q'.incidence i with ⟨_, hr⟩ | ⟨hl, _⟩
        · exact Or.inr hr
        · exact Or.inl hl
      exact q.vertex_mem_of_incident_edge (q.overlay_saturated hm hn he hend ih (he' i) hleft) hright
  intro e heq
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp heq
  apply q.overlay_saturated hm hn he hend (hv i.castSucc) (he' i)
  rcases q'.incidence i with ⟨hl, _⟩ | ⟨_, hr⟩
  · exact Or.inl hl
  · exact Or.inr hr

/-- The edge identities of the endpoint-to-endpoint path are unique. -/
theorem edgeSet_eq_of_same_start (q : SimpleEdgePath G r) (q' : SimpleEdgePath G s)
    {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (he : ∀ i, q.edge i ∈ m ∆ n) (he' : ∀ i, q'.edge i ∈ m ∆ n)
    (hend : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    (hend' : ∀ v, v = q'.vertex 0 ∨ v = q'.vertex (Fin.last (s + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    (hstart : q'.vertex 0 = q.vertex 0) : q.edgeSet = q'.edgeSet :=
  Finset.Subset.antisymm (q'.edges_subset_of_same_start q hm hn he' he hend' hstart.symm)
    (q.edges_subset_of_same_start q' hm hn he he' hend hstart)

end SimpleEdgePath

namespace SimpleEdgePath

variable {G : WeightedGraph V E K} {r s : ℕ}

@[simp] theorem degree_end (q : SimpleEdgePath G r) :
    matchingDegree G q.edgeSet (q.vertex (Fin.last (r + 1))) = 1 := by
  have hd := q.degree_add_endpoints (q.vertex (Fin.last (r + 1)))
  have hv : q.vertex (Fin.last (r + 1)) ∈ q.vertexSet :=
    Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  simp only [q.endpoints_distinct, ite_false, hv, ite_true, add_zero] at hd
  omega

/-- With the start fixed, the selected edge identities determine the other endpoint. -/
theorem end_eq_of_edgeSet_eq (q : SimpleEdgePath G r) (q' : SimpleEdgePath G s)
    (hstart : q'.vertex 0 = q.vertex 0) (hedges : q.edgeSet = q'.edgeSet) :
    q.vertex (Fin.last (r + 1)) = q'.vertex (Fin.last (s + 1)) := by
  have hd := q.degree_add_endpoints (q'.vertex (Fin.last (s + 1)))
  have hn : q.vertex 0 ≠ q'.vertex (Fin.last (s + 1)) := by
    rw [← hstart]
    exact q'.endpoints_distinct
  rw [hedges, q'.degree_end, ite_eq_right hn] at hd
  by_contra he
  rw [ite_eq_right he] at hd
  split_ifs at hd <;> omega

end SimpleEdgePath

/-- An endpoint path is specified by its other endpoint and its actual edge set.
Its existence data contains a simple path, not merely local degree constraints. -/
def IsOverlayEndpointPath (G : WeightedGraph V E K) (m n : Finset E)
    (a : V) (bp : V × Finset E) : Prop :=
  ∃ (r : ℕ) (q : SimpleEdgePath G r), q.vertex 0 = a ∧
    q.vertex (Fin.last (r + 1)) = bp.1 ∧ q.edgeSet = bp.2 ∧
    (∀ i, q.edge i ∈ m ∆ n) ∧
    (∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)

/-- Edge-color exchange preserves the uncolored endpoint-path predicate. -/
theorem isOverlayEndpointPath_switch_iff (G : WeightedGraph V E K)
    (m n p : Finset E) (a : V) (bp : V × Finset E) :
    IsOverlayEndpointPath G (switchEdges m n p) (switchEdges n m p) a bp ↔
      IsOverlayEndpointPath G m n a bp := by
  simp only [IsOverlayEndpointPath, switchEdges_symmDiff_switchEdges, matchingDegree_switchEdges_add]

/-- The endpoint and the selected edge identities are unique, even for multigraphs. -/
theorem IsOverlayEndpointPath.unique {G : WeightedGraph V E K} {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    {a : V} {bp cp : V × Finset E} (hb : IsOverlayEndpointPath G m n a bp)
    (hc : IsOverlayEndpointPath G m n a cp) : bp = cp := by
  obtain ⟨r, q, hs, he, hp, hqe, hqend⟩ := hb
  obtain ⟨s, q', hs', he', hp', hqe', hqend'⟩ := hc
  have hstart := hs'.trans hs.symm
  have hset := q.edgeSet_eq_of_same_start q' hm hn hqe hqe' hqend hqend' hstart
  have hend := q.end_eq_of_edgeSet_eq q' hstart hset
  apply Prod.ext
  · exact he.symm.trans (hend.trans he')
  · exact hp.symm.trans (hset.trans hp')

/-- Every degree-one endpoint supplies an endpoint path with uniquely determined
other endpoint and edge set. -/
theorem exists_isOverlayEndpointPath (G : WeightedGraph V E K) (m n : Finset E)
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (a : V) (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    ∃ bp, IsOverlayEndpointPath G m n a bp := by
  obtain ⟨r, q, hs, he, hend⟩ := exists_simpleEdgePath_from_overlay_endpoint G m n hm hn a ha
  refine ⟨(q.vertex (Fin.last (r + 1)), q.edgeSet), r, q, hs, rfl, rfl, he, ?_⟩
  intro v hv
  rcases hv with rfl | rfl
  · simpa [hs] using ha
  · exact hend

/-- A chosen endpoint path. The fallback is irrelevant when the starting endpoint
has degree one; on that domain both components of the choice are unique. -/
def overlayEndpointPath (G : WeightedGraph V E K) (m n : Finset E) (a : V) : V × Finset E :=
  if h : ∃ bp, IsOverlayEndpointPath G m n a bp then Classical.choose h else (a, ∅)

theorem overlayEndpointPath_spec_of_exists (G : WeightedGraph V E K) (m n : Finset E)
    (a : V) (h : ∃ bp, IsOverlayEndpointPath G m n a bp) :
    IsOverlayEndpointPath G m n a (overlayEndpointPath G m n a) := by
  unfold overlayEndpointPath
  rw [dite_eq_left h]
  exact Classical.choose_spec h

theorem overlayEndpointPath_spec (G : WeightedGraph V E K) (m n : Finset E)
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (a : V) (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    IsOverlayEndpointPath G m n a (overlayEndpointPath G m n a) :=
  overlayEndpointPath_spec_of_exists G m n a (exists_isOverlayEndpointPath G m n hm hn a ha)

/-- The constructed endpoint path supplies the switch certificate. -/
theorem IsOverlayEndpointPath.certificate {G : WeightedGraph V E K}
    {m n : Finset E} {a : V} {bp : V × Finset E}
    (h : IsOverlayEndpointPath G m n a bp) : AlternatingPathEdges G m n bp.2 a bp.1 := by
  obtain ⟨r, q, hs, he, hp, hqe, hqend⟩ := h
  have hc := q.alternatingPathEdges hqe hqend
  simpa only [hs, he, hp] using hc

/-- Path selection is invariant under exchanging any selected edge colors. This
uses uniqueness, so it is independent of the implementation of classical choice. -/
theorem overlayEndpointPath_switch (G : WeightedGraph V E K) (m n p : Finset E)
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (a : V) (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    overlayEndpointPath G (switchEdges m n p) (switchEdges n m p) a =
      overlayEndpointPath G m n a := by
  have horig := overlayEndpointPath_spec G m n hm hn a ha
  have hex : ∃ bp, IsOverlayEndpointPath G (switchEdges m n p) (switchEdges n m p) a bp :=
    ⟨_, (isOverlayEndpointPath_switch_iff G m n p a _).mpr horig⟩
  have hnew := overlayEndpointPath_spec_of_exists G _ _ a hex
  have hback := (isOverlayEndpointPath_switch_iff G m n p a _).mp hnew
  exact hback.unique hm hn horig

/-- A degree-one overlay endpoint is exactly a vertex active in one matching only. -/
theorem matchesExactly_overlay_endpoint_iff (G : WeightedGraph V E K)
    {A B : Finset V} {m n : Finset E} (hm : MatchesExactly G A m)
    (hn : MatchesExactly G B n) (a : V) :
    matchingDegree G m a + matchingDegree G n a = 1 ↔ a ∈ A ∆ B := by
  rw [hm a, hn a, Finset.mem_symmDiff]
  split_ifs <;> simp_all

/-- The endpoint switch selects its own uniquely determined simple path. -/
def endpointMatchingSwitch (G : WeightedGraph V E K) (a : V)
    (mn : Finset E × Finset E) : Finset E × Finset E :=
  let p := (overlayEndpointPath G mn.1 mn.2 a).2
  (switchEdges mn.1 mn.2 p, switchEdges mn.2 mn.1 p)

/-- Recomputing the path after the first switch gives the same edge identities;
therefore the constructed switch, rather than just a fixed-certificate switch,
is an involution on its matching domain. -/
theorem endpointMatchingSwitch_involutive (G : WeightedGraph V E K)
    (m n : Finset E) (hm : ∀ v, matchingDegree G m v ≤ 1)
    (hn : ∀ v, matchingDegree G n v ≤ 1) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    endpointMatchingSwitch G a (endpointMatchingSwitch G a (m, n)) = (m, n) := by
  dsimp only [endpointMatchingSwitch]
  rw [overlayEndpointPath_switch G m n _ hm hn a ha]
  simp only [switchEdges_involutive]

/-- The constructed switch preserves both matching conditions and toggles exactly
the original endpoint and the uniquely determined opposite endpoint. -/
theorem endpointMatchingSwitch_matchesExactly (G : WeightedGraph V E K)
    {A B : Finset V} {m n : Finset E} (hm : MatchesExactly G A m)
    (hn : MatchesExactly G B n) (a : V)
    (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    MatchesExactly G (A ∆ {a, (overlayEndpointPath G m n a).1})
        (endpointMatchingSwitch G a (m, n)).1 ∧
      MatchesExactly G (B ∆ {a, (overlayEndpointPath G m n a).1})
        (endpointMatchingSwitch G a (m, n)).2 := by
  have hm' (v : V) : matchingDegree G m v ≤ 1 := by rw [hm v]; split_ifs <;> omega
  have hn' (v : V) : matchingDegree G n v ≤ 1 := by rw [hn v]; split_ifs <;> omega
  exact (overlayEndpointPath_spec G m n hm' hn' a ha).certificate.matchesExactly_pair_switched hm hn

/-- Weight preservation for the constructed path switch needs only monoid weights. -/
theorem endpointMatchingSwitch_weight {R : Type*} [CommMonoid R] (w : E → R)
    (G : WeightedGraph V E K) (a : V) (mn : Finset E × Finset E) :
    (∏ e ∈ (endpointMatchingSwitch G a mn).1, w e) *
        (∏ e ∈ (endpointMatchingSwitch G a mn).2, w e) =
      (∏ e ∈ mn.1, w e) * (∏ e ∈ mn.2, w e) :=
  prod_switchEdges_mul_prod_switchEdges w mn.1 mn.2 _

/-- On its degree-one-endpoint domain the constructed involution has no fixed point. -/
theorem endpointMatchingSwitch_ne (G : WeightedGraph V E K) (m n : Finset E)
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (a : V) (ha : matchingDegree G m a + matchingDegree G n a = 1) :
    endpointMatchingSwitch G a (m, n) ≠ (m, n) := by
  intro h
  have hc := (overlayEndpointPath_spec G m n hm hn a ha).certificate
  exact hc.switchEdges_ne (congrArg Prod.fst h)

/-- Local switching also preserves the degree-at-most-one matching condition
without requiring an ambient finite vertex enumeration. -/
theorem AlternatingPathEdges.degree_le_one_switched {G : WeightedGraph V E K}
    {m n p : Finset E} {a b : V} (h : AlternatingPathEdges G m n p a b)
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (v : V) : matchingDegree G (switchEdges m n p) v ≤ 1 := by
  rw [matchingDegree_switchEdges]
  have hM := matchingDegree_inter_add_sdiff G m p v
  have hN := matchingDegree_inter_add_sdiff G n p v
  have hp := matchingDegree_eq_inter_add_inter G m n p h.in_overlay v
  have hm' := hm v
  have hn' := hn v
  by_cases hv : v = a ∨ v = b
  · have ho := h.endpoint_outside_degree v hv
    omega
  · have hi := h.interior_degree v (by tauto) (by tauto)
    omega

/-- Matching-pair domain with a distinguished degree-one overlay endpoint. -/
def EndpointMatchingPairs (G : WeightedGraph V E K) (a : V) :=
  { mn : Finset E × Finset E // (∀ v, matchingDegree G mn.1 v ≤ 1) ∧
    (∀ v, matchingDegree G mn.2 v ≤ 1) ∧
    matchingDegree G mn.1 a + matchingDegree G mn.2 a = 1 }

/-- The constructed switch restricts to its actual matching domain. -/
def endpointMatchingSwitchOn (G : WeightedGraph V E K) (a : V)
    (x : EndpointMatchingPairs G a) : EndpointMatchingPairs G a :=
  ⟨endpointMatchingSwitch G a x.val, by
    obtain ⟨hm, hn, ha⟩ := x.property
    have hp := (overlayEndpointPath_spec G x.val.1 x.val.2 hm hn a ha).certificate
    exact ⟨hp.degree_le_one_switched hm hn, hp.symm.degree_le_one_switched hn hm,
      (matchingDegree_switchEdges_add G x.val.1 x.val.2 _ a).trans ha⟩⟩

/-- A fixed-point-free, weight-preserving involutive equivalence on finite matching
pairs, using the uniquely constructed path rather than a supplied path certificate. -/
def endpointMatchingInvolution (G : WeightedGraph V E K) (a : V) :
    EndpointMatchingPairs G a ≃ EndpointMatchingPairs G a where
  toFun := endpointMatchingSwitchOn G a
  invFun := endpointMatchingSwitchOn G a
  left_inv := by
    intro x
    apply Subtype.ext
    exact endpointMatchingSwitch_involutive G x.val.1 x.val.2 x.property.1
      x.property.2.1 a x.property.2.2
  right_inv := by
    intro x
    apply Subtype.ext
    exact endpointMatchingSwitch_involutive G x.val.1 x.val.2 x.property.1
      x.property.2.1 a x.property.2.2

/-- The packaged equivalence has no fixed point. -/
theorem endpointMatchingInvolution_ne (G : WeightedGraph V E K) (a : V)
    (x : EndpointMatchingPairs G a) : endpointMatchingInvolution G a x ≠ x := by
  intro h
  exact endpointMatchingSwitch_ne G x.val.1 x.val.2 x.property.1 x.property.2.1 a
    x.property.2.2 (congrArg Subtype.val h)

end
end MatchgateWidth
