import MatchgateWidth.MatchingSignature
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite matching switches

A switch exchanges the ownership of specified *edge identities* in two finite
edge sets. Shared edges and parallel edges cause no ambiguity. The algebraic
switch is involutive and preserves the product of weights over any commutative
monoid, without cancellation or nonzero-weight assumptions.

The matching theorem uses a local incidence certificate: the selected edges lie
in the symmetric difference, have degree one at two degree-one overlay endpoints,
and degree zero or two elsewhere. It does not assume that the switched sets are
matchings. These conditions also allow disjoint alternating cycles, which do not
change the conclusion. The endpoint-component construction is proved in `MatchingOverlayPath`.
The boundary noncrossing parity needed for MGI remains a separate geometric task.
-/

namespace MatchgateWidth

noncomputable section

open Classical
open scoped symmDiff

variable {V E K : Type*}

/-- Exchange the edges selected by `p` from the second set into the first set. -/
def switchEdges (m n p : Finset E) : Finset E := (m \ p) ∪ (n ∩ p)

@[simp] theorem mem_switchEdges (m n p : Finset E) (e : E) :
    e ∈ switchEdges m n p ↔ if e ∈ p then e ∈ n else e ∈ m := by
  simp only [switchEdges, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  split_ifs <;> tauto

@[simp] theorem switchEdges_involutive (m n p : Finset E) :
    switchEdges (switchEdges m n p) (switchEdges n m p) p = m := by
  ext e
  simp only [mem_switchEdges]
  split_ifs <;> rfl

/-- The pair switch is a genuine involution on finite edge subsets. -/
def matchingSwitch (p : Finset E) : (Finset E × Finset E) ≃ (Finset E × Finset E) where
  toFun mn := (switchEdges mn.1 mn.2 p, switchEdges mn.2 mn.1 p)
  invFun mn := (switchEdges mn.1 mn.2 p, switchEdges mn.2 mn.1 p)
  left_inv := by rintro ⟨m, n⟩; simp
  right_inv := by rintro ⟨m, n⟩; simp

@[simp] theorem switchEdges_inter (m n p : Finset E) :
    switchEdges m n p ∩ p = n ∩ p := by
  ext e
  simp only [Finset.mem_inter, mem_switchEdges]
  split_ifs <;> tauto

@[simp] theorem switchEdges_sdiff (m n p : Finset E) :
    switchEdges m n p \ p = m \ p := by
  ext e
  simp only [Finset.mem_sdiff, mem_switchEdges]
  split_ifs <;> tauto

/-- Common edges remain common, and edges outside the switch remain unchanged. -/
theorem switchEdges_inter_switchEdges (m n p : Finset E) :
    switchEdges m n p ∩ switchEdges n m p = m ∩ n := by
  ext e
  simp only [Finset.mem_inter, mem_switchEdges]
  split_ifs <;> tauto

/-- The uncolored overlay is unchanged by the switch. -/
theorem switchEdges_symmDiff_switchEdges (m n p : Finset E) :
    switchEdges m n p ∆ switchEdges n m p = m ∆ n := by
  ext e
  simp only [Finset.mem_symmDiff, mem_switchEdges]
  split_ifs <;> tauto

/-- On edges in the symmetric difference, ownership exchange is ordinary toggling. -/
theorem switchEdges_eq_symmDiff (m n p : Finset E) (hp : p ⊆ m ∆ n) :
    switchEdges m n p = m ∆ p := by
  ext e
  have he := fun h : e ∈ p => Finset.mem_symmDiff.mp (hp h)
  simp only [mem_switchEdges, Finset.mem_symmDiff]
  split_ifs <;> tauto

/-- Weight-product preservation needs only a commutative monoid. -/
theorem prod_switchEdges_mul_prod_switchEdges {R : Type*} [CommMonoid R]
    (w : E → R) (m n p : Finset E) :
    (∏ e ∈ switchEdges m n p, w e) * (∏ e ∈ switchEdges n m p, w e) =
      (∏ e ∈ m, w e) * (∏ e ∈ n, w e) := by
  have hd (s t : Finset E) : Disjoint (s \ p) (t ∩ p) := by
    exact Finset.disjoint_left.mpr (by simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto)
  simp only [switchEdges, Finset.prod_union (hd m n), Finset.prod_union (hd n m)]
  rw [← Finset.prod_inter_mul_prod_sdiff m p w, ← Finset.prod_inter_mul_prod_sdiff n p w]
  ac_rfl

/-- Degrees split additively across the switch region. -/
theorem matchingDegree_inter_add_sdiff (G : WeightedGraph V E K)
    (m p : Finset E) (v : V) :
    matchingDegree G (m ∩ p) v + matchingDegree G (m \ p) v =
      matchingDegree G m v := by
  exact Finset.sum_inter_add_sum_sdiff m p _

/-- Incidence formula before imposing any matching hypothesis. -/
theorem matchingDegree_switchEdges (G : WeightedGraph V E K)
    (m n p : Finset E) (v : V) :
    matchingDegree G (switchEdges m n p) v =
      matchingDegree G (m \ p) v + matchingDegree G (n ∩ p) v := by
  apply Finset.sum_union
  exact Finset.disjoint_left.mpr (by simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto)

/-- The sum of the two incidence degrees is conserved at every vertex. -/
theorem matchingDegree_switchEdges_add (G : WeightedGraph V E K)
    (m n p : Finset E) (v : V) :
    matchingDegree G (switchEdges m n p) v + matchingDegree G (switchEdges n m p) v =
      matchingDegree G m v + matchingDegree G n v := by
  rw [matchingDegree_switchEdges, matchingDegree_switchEdges]
  have hm := matchingDegree_inter_add_sdiff G m p v
  have hn := matchingDegree_inter_add_sdiff G n p v
  omega

/-- A subgraph of the symmetric difference splits into its two edge colors. -/
theorem matchingDegree_eq_inter_add_inter (G : WeightedGraph V E K)
    (m n p : Finset E) (hp : p ⊆ m ∆ n) (v : V) :
    matchingDegree G p v = matchingDegree G (m ∩ p) v + matchingDegree G (n ∩ p) v := by
  have hu : p = (m ∩ p) ∪ (n ∩ p) := by
    ext e
    have he := fun h : e ∈ p => Finset.mem_symmDiff.mp (hp h)
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hd : Disjoint (m ∩ p) (n ∩ p) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    have hs := Finset.mem_symmDiff.mp (hp (Finset.mem_inter.mp he).2)
    simp only [Finset.mem_inter] at he hf
    tauto
  conv_lhs => rw [hu]
  exact Finset.sum_union hd

/-- A purely local certificate sufficient for switching a two-ended alternating
edge set. A connected alternating path supplies these conditions, but connectedness
is not required: disjoint alternating cycles are harmless. -/
structure AlternatingPathEdges (G : WeightedGraph V E K) (m n p : Finset E)
    (a b : V) : Prop where
  distinct : a ≠ b
  in_overlay : p ⊆ m ∆ n
  endpoint_degree : ∀ v, v = a ∨ v = b → matchingDegree G p v = 1
  interior_degree : ∀ v, v ≠ a → v ≠ b →
    matchingDegree G p v = 0 ∨ matchingDegree G p v = 2
  overlay_endpoint_degree : ∀ v, v = a ∨ v = b →
    matchingDegree G m v + matchingDegree G n v = 1

namespace AlternatingPathEdges

variable {G : WeightedGraph V E K} {m n p : Finset E} {a b : V}

/-- The certificate is symmetric in the two colors. -/
theorem symm (h : AlternatingPathEdges G m n p a b) :
    AlternatingPathEdges G n m p a b where
  distinct := h.distinct
  in_overlay := by simpa [symmDiff_comm] using h.in_overlay
  endpoint_degree := h.endpoint_degree
  interior_degree := h.interior_degree
  overlay_endpoint_degree := by intro v hv; simpa [add_comm] using h.overlay_endpoint_degree v hv

/-- At an endpoint all incident overlay edges are in the switch. -/
theorem endpoint_outside_degree (h : AlternatingPathEdges G m n p a b)
    (v : V) (hv : v = a ∨ v = b) :
    matchingDegree G (m \ p) v = 0 ∧ matchingDegree G (n \ p) v = 0 := by
  have hp := matchingDegree_eq_inter_add_inter G m n p h.in_overlay v
  have hm := matchingDegree_inter_add_sdiff G m p v
  have hn := matchingDegree_inter_add_sdiff G n p v
  have he := h.endpoint_degree v hv
  have ho := h.overlay_endpoint_degree v hv
  omega

/-- The edge-set certificate remains valid after switching, independently of weights. -/
theorem switched (h : AlternatingPathEdges G m n p a b) :
    AlternatingPathEdges G (switchEdges m n p) (switchEdges n m p) p a b where
  distinct := h.distinct
  in_overlay := by rw [switchEdges_symmDiff_switchEdges]; exact h.in_overlay
  endpoint_degree := h.endpoint_degree
  interior_degree := h.interior_degree
  overlay_endpoint_degree := by
    intro v hv
    rw [matchingDegree_switchEdges_add]
    exact h.overlay_endpoint_degree v hv

/-- Two matchings force alternation at every non-endpoint of the certificate. -/
theorem interior_balanced (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n)
    (v : V) (ha : v ≠ a) (hb : v ≠ b) :
    matchingDegree G (m ∩ p) v = matchingDegree G (n ∩ p) v := by
  have hp := matchingDegree_eq_inter_add_inter G m n p h.in_overlay v
  have hm' := matchingDegree_inter_add_sdiff G m p v
  have hn' := matchingDegree_inter_add_sdiff G n p v
  have hm'' : matchingDegree G m v ≤ 1 := by rw [hm v]; split_ifs <;> omega
  have hn'' : matchingDegree G n v ≤ 1 := by rw [hn v]; split_ifs <;> omega
  have hi := h.interior_degree v ha hb
  omega

/-- The switch swaps the degrees at exactly the two endpoints. -/
theorem degree_switched (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n) (v : V) :
    matchingDegree G (switchEdges m n p) v =
      if v = a ∨ v = b then matchingDegree G n v else matchingDegree G m v := by
  rw [matchingDegree_switchEdges]
  split_ifs with hv
  · obtain ⟨hoM, hoN⟩ := h.endpoint_outside_degree v hv
    have hi := matchingDegree_inter_add_sdiff G n p v
    omega
  · have hb := h.interior_balanced hm hn v (by tauto) (by tauto)
    have hi := matchingDegree_inter_add_sdiff G m p v
    omega

/-- Each endpoint belongs to exactly one of the two active sets. -/
theorem endpoint_active_exclusive (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n)
    (v : V) (hv : v = a ∨ v = b) :
    (v ∈ A ∧ v ∉ B) ∨ (v ∈ B ∧ v ∉ A) := by
  have he := h.overlay_endpoint_degree v hv
  rw [hm v, hn v] at he
  split_ifs at he <;> simp_all

/-- Toggling the two endpoint states produces another actual matching. -/
theorem matchesExactly_switched (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n) :
    MatchesExactly G (A ∆ {a, b}) (switchEdges m n p) := by
  intro v
  rw [h.degree_switched hm hn v]
  by_cases hv : v = a ∨ v = b
  · have he := h.endpoint_active_exclusive hm hn v hv
    simp only [ite_eq_left hv, hn v, Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton]
    rcases he with ⟨ha, hb⟩ | ⟨hb, ha⟩ <;> simp [ha, hb, hv]
  · simp only [ite_eq_right hv, hm v, Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton]
    simp [hv]

/-- Both matching conditions are preserved, with only the endpoint states toggled. -/
theorem matchesExactly_pair_switched (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n) :
    MatchesExactly G (A ∆ {a, b}) (switchEdges m n p) ∧
      MatchesExactly G (B ∆ {a, b}) (switchEdges n m p) :=
  ⟨h.matchesExactly_switched hm hn, h.symm.matchesExactly_switched hn hm⟩

/-- A two-ended certificate has a nonempty selected edge set. -/
theorem nonempty (h : AlternatingPathEdges G m n p a b) : p.Nonempty := by
  by_contra hp
  have he := h.endpoint_degree a (Or.inl rfl)
  have hp' : p = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
  simp [hp', matchingDegree] at he

/-- A switch with a degree-one endpoint cannot leave either edge color fixed. -/
theorem switchEdges_ne (h : AlternatingPathEdges G m n p a b) :
    switchEdges m n p ≠ m := by
  intro hs
  obtain ⟨hoM, hoN⟩ := h.endpoint_outside_degree a (Or.inl rfl)
  have hd := matchingDegree_switchEdges G m n p a
  have hn := matchingDegree_inter_add_sdiff G n p a
  have he := h.overlay_endpoint_degree a (Or.inl rfl)
  rw [hs] at hd
  omega

/-- The usual path-toggle formulation, derived from ownership exchange. -/
theorem matchesExactly_symmDiff (h : AlternatingPathEdges G m n p a b)
    {A B : Finset V} (hm : MatchesExactly G A m) (hn : MatchesExactly G B n) :
    MatchesExactly G (A ∆ {a, b}) (m ∆ p) ∧
      MatchesExactly G (B ∆ {a, b}) (n ∆ p) := by
  have hs := h.matchesExactly_pair_switched hm hn
  rw [switchEdges_eq_symmDiff m n p h.in_overlay,
    switchEdges_eq_symmDiff n m p h.symm.in_overlay] at hs
  exact hs

end AlternatingPathEdges

/-- A finite matching pair together with the local certificate for a fixed switch. -/
def CertifiedMatchingPair (G : WeightedGraph V E K) (A B : Finset V)
    (p : Finset E) (a b : V) :=
  { mn : Finset E × Finset E // MatchesExactly G A mn.1 ∧
    MatchesExactly G B mn.2 ∧ AlternatingPathEdges G mn.1 mn.2 p a b }

/-- The certified switch is an equivalence of actual matching-pair types. -/
def certifiedMatchingSwitch (G : WeightedGraph V E K) (A B : Finset V)
    (p : Finset E) (a b : V) :
    CertifiedMatchingPair G A B p a b ≃
      CertifiedMatchingPair G (A ∆ {a, b}) (B ∆ {a, b}) p a b where
  toFun x := ⟨(switchEdges x.val.1 x.val.2 p, switchEdges x.val.2 x.val.1 p),
    x.property.2.2.matchesExactly_switched x.property.1 x.property.2.1,
    x.property.2.2.symm.matchesExactly_switched x.property.2.1 x.property.1,
    x.property.2.2.switched⟩
  invFun x := ⟨(switchEdges x.val.1 x.val.2 p, switchEdges x.val.2 x.val.1 p), by
    obtain ⟨hm, hn, hp⟩ := x.property
    have hs := hp.matchesExactly_pair_switched hm hn
    simpa only [symmDiff_symmDiff_cancel_right] using And.intro hs.1 (And.intro hs.2 hp.switched)⟩
  left_inv := by intro x; apply Subtype.ext; simp
  right_inv := by intro x; apply Subtype.ext; simp

/-- The certified equivalence preserves the matching weight product. No semiring
or cancellation law is needed even for this packaged form. -/
theorem certifiedMatchingSwitch_weight {R : Type*} [CommMonoid R]
    (w : E → R) (G : WeightedGraph V E K) (A B : Finset V)
    (p : Finset E) (a b : V) (x : CertifiedMatchingPair G A B p a b) :
    (∏ e ∈ (certifiedMatchingSwitch G A B p a b x).val.1, w e) *
        (∏ e ∈ (certifiedMatchingSwitch G A B p a b x).val.2, w e) =
      (∏ e ∈ x.val.1, w e) * (∏ e ∈ x.val.2, w e) :=
  prod_switchEdges_mul_prod_switchEdges w x.val.1 x.val.2 p

/-- A positive-length simple path retaining its actual edge identities and allowing
arbitrary edge orientations. The index `r` is the number of internal vertices. -/
structure SimpleEdgePath (G : WeightedGraph V E K) (r : ℕ) where
  vertex : Fin (r + 2) → V
  edge : Fin (r + 1) → E
  vertex_injective : Function.Injective vertex
  edge_injective : Function.Injective edge
  incidence : ∀ i,
    (G.left (edge i) = vertex i.castSucc ∧ G.right (edge i) = vertex i.succ) ∨
    (G.left (edge i) = vertex i.succ ∧ G.right (edge i) = vertex i.castSucc)

namespace SimpleEdgePath

variable {G : WeightedGraph V E K} {r : ℕ}

/-- The finite selected edge identities of the path. -/
def edgeSet (q : SimpleEdgePath G r) : Finset E := Finset.univ.image q.edge

/-- The finite vertices of the path. -/
def vertexSet (q : SimpleEdgePath G r) : Finset V := Finset.univ.image q.vertex

/-- Incidences of a simple path have the expected endpoint correction. This is a
natural-number identity, so it does not impose assumptions on coefficient weights. -/
theorem degree_add_endpoints (q : SimpleEdgePath G r) (v : V) :
    matchingDegree G q.edgeSet v + (if q.vertex 0 = v then 1 else 0) +
      (if q.vertex (Fin.last (r + 1)) = v then 1 else 0) =
        2 * (if v ∈ q.vertexSet then 1 else 0) := by
  have hd : matchingDegree G q.edgeSet v =
      ∑ i : Fin (r + 1), ((if q.vertex i.castSucc = v then 1 else 0) +
        (if q.vertex i.succ = v then 1 else 0)) := by
    unfold matchingDegree edgeSet
    rw [Finset.sum_image (fun _ _ _ _ h => q.edge_injective h)]
    apply Finset.sum_congr rfl
    intro i _
    rcases q.incidence i with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · rw [hl, hr]
    · rw [hl, hr, add_comm]
  have hs : (∑ i : Fin (r + 2), if q.vertex i = v then (1 : ℕ) else 0) =
      if v ∈ q.vertexSet then 1 else 0 := by
    unfold vertexSet
    rw [← Finset.sum_image (s := Finset.univ) (g := q.vertex)
      (f := fun w => if w = v then (1 : ℕ) else 0)
      (fun _ _ _ _ h => q.vertex_injective h)]
    simp
  have hf := Fin.sum_univ_succ (fun i : Fin (r + 2) => if q.vertex i = v then (1 : ℕ) else 0)
  have hl := Fin.sum_univ_castSucc (fun i : Fin (r + 2) => if q.vertex i = v then (1 : ℕ) else 0)
  rw [hd, Finset.sum_add_distrib]
  calc
    _ = ((if q.vertex 0 = v then 1 else 0) +
          ∑ i : Fin (r + 1), if q.vertex i.succ = v then 1 else 0) +
        ((∑ i : Fin (r + 1), if q.vertex i.castSucc = v then 1 else 0) +
          (if q.vertex (Fin.last (r + 1)) = v then 1 else 0)) := by ac_rfl
    _ = _ := by rw [← hf, ← hl, hs]; omega

/-- The two endpoints of a positive-length simple path are distinct. -/
theorem endpoints_distinct (q : SimpleEdgePath G r) :
    q.vertex 0 ≠ q.vertex (Fin.last (r + 1)) := by
  intro h
  have hf := congrArg Fin.val (q.vertex_injective h)
  simp at hf

/-- An explicitly given simple path in the symmetric-difference overlay supplies
all the local switch conditions. Only the endpoint overlay degrees are additional. -/
theorem alternatingPathEdges (q : SimpleEdgePath G r) {m n : Finset E}
    (hedges : ∀ i, q.edge i ∈ m ∆ n)
    (hendpoints : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1) :
    AlternatingPathEdges G m n q.edgeSet (q.vertex 0) (q.vertex (Fin.last (r + 1))) where
  distinct := q.endpoints_distinct
  in_overlay := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact hedges i
  endpoint_degree := by
    intro v hv
    have hd := q.degree_add_endpoints v
    have hn := q.endpoints_distinct
    rcases hv with rfl | rfl
    · have hm : q.vertex 0 ∈ q.vertexSet := Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      simp only [hm, ite_true, Ne.symm hn, ite_false] at hd
      omega
    · have hm : q.vertex (Fin.last (r + 1)) ∈ q.vertexSet :=
        Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
      simp only [hn, ite_false, hm, ite_true] at hd
      omega
  interior_degree := by
    intro v ha hb
    have hd := q.degree_add_endpoints v
    simp only [Ne.symm ha, Ne.symm hb, ite_false, add_zero] at hd
    split_ifs at hd <;> omega
  overlay_endpoint_degree := hendpoints

end SimpleEdgePath

end
end MatchgateWidth
