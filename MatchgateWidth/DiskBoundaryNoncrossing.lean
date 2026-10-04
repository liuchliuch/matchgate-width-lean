import MatchgateWidth.DiskPathLogarithm
import MatchgateWidth.MatchingBoundaryIdentity
import Mathlib.Topology.Connected.PathConnected

/-!
# From graph endpoint paths to disjoint continuous disk paths

This file makes the graph-to-topology reduction explicit. Actual endpoint paths
in an overlay with different endpoint pairs have disjoint vertex sets. Under a
`PlanarDrawing`, their geometric edge supports are disjoint, and the endpoint
vertices are joined by continuous paths inside those supports.

The purely topological disk crossing theorem is proved using exponential
covering-space lifting in `DiskPathLogarithm`. Combining the two establishes
boundary noncrossing and all matchgate identities for actual disk-drawn weighted
graph deletion signatures, without adding assumptions to `PlanarDrawing`.
-/

namespace MatchgateWidth
noncomputable section
open Classical
open scoped symmDiff

namespace SimpleEdgePath
variable {V E K : Type*} {G : WeightedGraph V E K} {r t : ℕ}

/-- An overlay endpoint path contains every vertex of another overlay path as
soon as it contains one. Saturation propagates in both directions along edges. -/
theorem vertex_mem_iff_of_overlay (q : SimpleEdgePath G r) (q' : SimpleEdgePath G t)
    {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (he : ∀ i, q.edge i ∈ m ∆ n) (he' : ∀ i, q'.edge i ∈ m ∆ n)
    (hend : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    (i : Fin (t + 2)) : q'.vertex i ∈ q.vertexSet ↔ q'.vertex 0 ∈ q.vertexSet := by
  have step (j : Fin (t + 1)) :
      q'.vertex j.castSucc ∈ q.vertexSet ↔ q'.vertex j.succ ∈ q.vertexSet := by
    have hl : G.left (q'.edge j) = q'.vertex j.castSucc ∨
        G.right (q'.edge j) = q'.vertex j.castSucc := by
      rcases q'.incidence j with ⟨h, _⟩ | ⟨_, h⟩
      · exact Or.inl h
      · exact Or.inr h
    have hr : G.left (q'.edge j) = q'.vertex j.succ ∨
        G.right (q'.edge j) = q'.vertex j.succ := by
      rcases q'.incidence j with ⟨_, h⟩ | ⟨h, _⟩
      · exact Or.inr h
      · exact Or.inl h
    exact ⟨fun hv => q.vertex_mem_of_incident_edge
        (q.overlay_saturated hm hn he hend hv (he' j) hl) hr,
      fun hv => q.vertex_mem_of_incident_edge
        (q.overlay_saturated hm hn he hend hv (he' j) hr) hl⟩
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (step i).symm.trans ih

/-- In an overlay of two matchings, endpoint paths starting away from one
another's two endpoints have disjoint vertex sets. -/
theorem vertexSet_disjoint_of_endpoint_paths (q : SimpleEdgePath G r)
    (q' : SimpleEdgePath G t) {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    (he : ∀ i, q.edge i ∈ m ∆ n) (he' : ∀ i, q'.edge i ∈ m ∆ n)
    (hend : ∀ v, v = q.vertex 0 ∨ v = q.vertex (Fin.last (r + 1)) →
      matchingDegree G m v + matchingDegree G n v = 1)
    (hstart' : matchingDegree G m (q'.vertex 0) + matchingDegree G n (q'.vertex 0) = 1)
    (h₀ : q'.vertex 0 ≠ q.vertex 0)
    (h₁ : q'.vertex 0 ≠ q.vertex (Fin.last (r + 1))) :
    Disjoint q.vertexSet q'.vertexSet := by
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv'
  have hmem := (q.vertex_mem_iff_of_overlay q' hm hn he he' hend i).mp hv
  have hdeg := q.degree_add_endpoints (q'.vertex 0)
  have hsubset : q.edgeSet ⊆ m ∆ n := by
    intro e heq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp heq
    exact he j
  have hle := matchingDegree_le_overlay G hsubset (q'.vertex 0)
  simp only [Ne.symm h₀, Ne.symm h₁, ite_false, hmem, ite_true, add_zero] at hdeg
  omega
end SimpleEdgePath

namespace PlanarDrawing
variable {V E : Type*} {s r t : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}

/-- The geometric support of the actual edge identities of a graph path. -/
def pathSupport (D : PlanarDrawing G ext) (q : SimpleEdgePath G r) : Set ℂ :=
  {z | ∃ e ∈ q.edgeSet, z ∈ Set.range (D.edge e)}

theorem pathSupport_in_disk (D : PlanarDrawing G ext) (q : SimpleEdgePath G r)
    {z : ℂ} (hz : z ∈ D.pathSupport q) : ‖z‖ ≤ 1 := by
  obtain ⟨e, _, u, rfl⟩ := hz
  exact D.edge_in_disk e u

/-- A point of an edge that is a vertex must be one of that edge's endpoints. -/
theorem vertex_incident_of_mem_edge (D : PlanarDrawing G ext) {e : E} {v : V}
    {u : unitInterval} (h : D.edge e u = D.vertex v) :
    G.left e = v ∨ G.right e = v := by
  by_cases h₀ : u = 0
  · left
    rw [h₀, D.edge_left] at h
    exact D.vertex_injective h
  by_cases h₁ : u = 1
  · right
    rw [h₁, D.edge_right] at h
    exact D.vertex_injective h
  exact (D.interior_avoids_vertices e u
    (lt_of_le_of_ne (show 0 ≤ u from u.property.1) (Ne.symm h₀))
    (lt_of_le_of_ne (show u ≤ 1 from u.property.2) h₁) v h).elim

/-- Intersecting edge images in a crossing-free drawing share an endpoint. -/
theorem common_vertex_of_edge_intersection (D : PlanarDrawing G ext) {e f : E}
    {u v : unitInterval} (h : D.edge e u = D.edge f v) :
    ∃ w, (G.left e = w ∨ G.right e = w) ∧ (G.left f = w ∨ G.right f = w) := by
  by_cases hef : e = f
  · subst f
    exact ⟨G.left e, Or.inl rfl, Or.inl rfl⟩
  by_cases hu₀ : u = 0
  · rw [hu₀, D.edge_left] at h
    exact ⟨G.left e, Or.inl rfl, D.vertex_incident_of_mem_edge h.symm⟩
  by_cases hu₁ : u = 1
  · rw [hu₁, D.edge_right] at h
    exact ⟨G.right e, Or.inr rfl, D.vertex_incident_of_mem_edge h.symm⟩
  by_cases hv₀ : v = 0
  · rw [hv₀, D.edge_left] at h
    exact ⟨G.left f, D.vertex_incident_of_mem_edge h, Or.inl rfl⟩
  by_cases hv₁ : v = 1
  · rw [hv₁, D.edge_right] at h
    exact ⟨G.right f, D.vertex_incident_of_mem_edge h, Or.inr rfl⟩
  exact (D.interiors_disjoint e f hef u v
    (lt_of_le_of_ne (show 0 ≤ u from u.property.1) (Ne.symm hu₀))
    (lt_of_le_of_ne (show u ≤ 1 from u.property.2) hu₁)
    (lt_of_le_of_ne (show 0 ≤ v from v.property.1) (Ne.symm hv₀))
    (lt_of_le_of_ne (show v ≤ 1 from v.property.2) hv₁) h).elim

/-- Vertex-disjoint actual graph paths have disjoint geometric edge supports. -/
theorem pathSupport_disjoint (D : PlanarDrawing G ext) (q : SimpleEdgePath G r)
    (q' : SimpleEdgePath G t) (hd : Disjoint q.vertexSet q'.vertexSet) :
    Disjoint (D.pathSupport q) (D.pathSupport q') := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨e, he, u, hu⟩ := hz
  obtain ⟨f, hf, v, hv⟩ := hz'
  obtain ⟨w, hwe, hwf⟩ := D.common_vertex_of_edge_intersection (hu.trans hv.symm)
  exact Finset.disjoint_left.mp hd (q.vertex_mem_of_incident_edge he hwe)
    (q'.vertex_mem_of_incident_edge hf hwf)

/-- A drawn edge is a continuous path, including its specified orientation. -/
def edgePath (D : PlanarDrawing G ext) (e : E) :
    Path (D.vertex (G.left e)) (D.vertex (G.right e)) where
  toFun := D.edge e
  continuous_toFun := D.edge_continuous e
  source' := D.edge_left e
  target' := D.edge_right e

/-- Every simple graph path is realized by a continuous path in its edge support.
Only finite concatenation is used; no planar separation theorem enters here. -/
theorem joinedIn_pathSupport (D : PlanarDrawing G ext) (q : SimpleEdgePath G r) :
    JoinedIn (D.pathSupport q) (D.vertex (q.vertex 0))
      (D.vertex (q.vertex (Fin.last (r + 1)))) := by
  have edge_join (i : Fin (r + 1)) : JoinedIn (D.pathSupport q)
      (D.vertex (q.vertex i.castSucc)) (D.vertex (q.vertex i.succ)) := by
    have hj : JoinedIn (D.pathSupport q)
        (D.vertex (G.left (q.edge i))) (D.vertex (G.right (q.edge i))) := by
      refine ⟨D.edgePath (q.edge i), ?_⟩
      intro u
      exact ⟨q.edge i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, u, rfl⟩
    rcases q.incidence i with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · simpa only [hl, hr] using hj
    · simpa only [hl, hr] using hj.symm
  have hall (i : Fin (r + 2)) : JoinedIn (D.pathSupport q)
      (D.vertex (q.vertex 0)) (D.vertex (q.vertex i)) := by
    induction i using Fin.induction with
    | zero => exact JoinedIn.refl (edge_join 0).source_mem
    | succ i ih => exact ih.trans (edge_join i)
  exact hall _

end PlanarDrawing

/-- Actual distinct overlay endpoint paths are realized by disjoint continuous
paths in the closed disk. This theorem assumes no plane separation principle. -/
theorem IsOverlayEndpointPath.disjoint_disk_paths
    {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}
    (D : PlanarDrawing G ext) {m n : Finset E}
    (hm : ∀ v, matchingDegree G m v ≤ 1) (hn : ∀ v, matchingDegree G n v ≤ 1)
    {a b c d : V} {p p' : Finset E}
    (h : IsOverlayEndpointPath G m n a (c, p))
    (h' : IsOverlayEndpointPath G m n b (d, p')) (hba : b ≠ a) (hbc : b ≠ c) :
    ∃ (γ : Path (D.vertex a) (D.vertex c)) (δ : Path (D.vertex b) (D.vertex d)),
      (∀ u, ‖γ u‖ ≤ 1) ∧ (∀ u, ‖δ u‖ ≤ 1) ∧
        Disjoint (Set.range γ) (Set.range δ) := by
  obtain ⟨r, q, hs, ht, _, he, hend⟩ := h
  obtain ⟨t, q', hs', ht', _, he', hend'⟩ := h'
  have hd := q.vertexSet_disjoint_of_endpoint_paths q' hm hn he he' hend
    (hend' _ (Or.inl rfl)) (by simpa only [hs, hs'] using hba)
    (by simpa only [ht, hs'] using hbc)
  have hj := D.joinedIn_pathSupport q
  have hj' := D.joinedIn_pathSupport q'
  rw [hs, ht] at hj
  rw [hs', ht'] at hj'
  obtain ⟨γ, hγ⟩ := hj
  obtain ⟨δ, hδ⟩ := hj'
  refine ⟨γ, δ, fun u => D.pathSupport_in_disk q (hγ u),
    fun u => D.pathSupport_in_disk q' (hδ u), ?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨u, rfl⟩ ⟨v, hv⟩
  exact Set.disjoint_left.mp (D.pathSupport_disjoint q q' hd) (hγ u) (hv ▸ hδ v)

/-- The disk crossing statement for the turn-valued boundary coordinates used
by `PlanarDrawing`. No path injectivity is required. Proved below. -/
def DiskPathCrossing : Prop :=
  ∀ (a b c d : ℝ), 0 < a → a < b → b < c → c < d → d < 1 →
    ∀ (γ : Path (boundaryPoint a) (boundaryPoint c))
      (δ : Path (boundaryPoint b) (boundaryPoint d)),
      (∀ u, ‖γ u‖ ≤ 1) → (∀ u, ‖δ u‖ ≤ 1) →
      ∃ u v, γ u = δ v

/-- Crossing for the exact boundary coordinates of disk drawings, derived from
covering-space lifting rather than assumed as a geometric axiom. -/
theorem diskPathCrossing : DiskPathCrossing := by
  intro a b c d ha hab hbc hcd hd γ δ hγ hδ
  have hpoint (x : ℝ) : boundaryPoint x = Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I) := by
    simp [boundaryPoint, circleMap]
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  exact disk_paths_cross_radians
    (mul_lt_mul_of_pos_left hab hp) (mul_lt_mul_of_pos_left hbc hp)
    (mul_lt_mul_of_pos_left hcd hp)
    (by have h := mul_lt_mul_of_pos_left (show d < a + 1 by linarith) hp; nlinarith)
    (γ.cast (hpoint a).symm (hpoint c).symm)
    (δ.cast (hpoint b).symm (hpoint d).symm) hγ hδ

/-- The graph-to-topology reduction, also available with an explicit crossing
principle for reuse with alternative proofs of that topological theorem. -/
theorem PlanarDrawing.boundaryPathNoncrossing_of_diskPathCrossing
    (crossing : DiskPathCrossing)
    {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}
    (D : PlanarDrawing G ext) : BoundaryPathNoncrossing G ext := by
  intro m n hm hn a b c d p q hp hq hab hbc hcd
  obtain ⟨γ, δ, hγ, hδ, hd⟩ := hp.disjoint_disk_paths D hm hn hq
    (fun h => (ne_of_gt hab) (D.external_injective h))
    (fun h => (ne_of_lt hbc) (D.external_injective h))
  obtain ⟨u, v, huv⟩ := crossing (D.angle a) (D.angle b) (D.angle c) (D.angle d)
    (D.angle_pos a) (D.angle_strictMono hab) (D.angle_strictMono hbc)
    (D.angle_strictMono hcd) (D.angle_lt_one d)
    (γ.cast (D.external_vertex a).symm (D.external_vertex c).symm)
    (δ.cast (D.external_vertex b).symm (D.external_vertex d).symm) hγ hδ
  exact Set.disjoint_left.mp hd ⟨u, rfl⟩ ⟨v, huv.symm⟩

/-- The reduction for the original graph deletion signature with its crossing
principle displayed explicitly. The unconditional theorem follows below. -/
theorem PlanarDrawing.deletionSignature_matchgateIdentities_of_diskPathCrossing
    (crossing : DiskPathCrossing)
    {V E : Type*} [Fintype V] [Fintype E] {s : ℕ}
    {G : WeightedGraph V E ℂ} {ext : Fin s → V} (D : PlanarDrawing G ext) :
    MatchgateIdentities (fun S => deletionSignature G ext (fun i => decide (i ∈ S))) :=
  deletionSignature_matchgateIdentities G ext D.external_injective
    (D.boundaryPathNoncrossing_of_diskPathCrossing crossing)

/-- Genuine continuous disk drawings force actual overlay endpoint paths to be
noncrossing in the prescribed external order. -/
theorem PlanarDrawing.boundaryPathNoncrossing
    {V E : Type*} {s : ℕ} {G : WeightedGraph V E ℂ} {ext : Fin s → V}
    (D : PlanarDrawing G ext) : BoundaryPathNoncrossing G ext :=
  D.boundaryPathNoncrossing_of_diskPathCrossing diskPathCrossing

/-- All matchgate identities for an actual disk-drawn weighted graph, with the
original Boolean boundary-deletion convention. -/
theorem PlanarDrawing.deletionSignature_matchgateIdentities
    {V E : Type*} [Fintype V] [Fintype E] {s : ℕ}
    {G : WeightedGraph V E ℂ} {ext : Fin s → V} (D : PlanarDrawing G ext) :
    MatchgateIdentities (fun S => deletionSignature G ext (fun i => decide (i ∈ S))) :=
  D.deletionSignature_matchgateIdentities_of_diskPathCrossing diskPathCrossing

/-- The finite-subset presentation of the same exact disk matching sum. -/
theorem PlanarDrawing.deletionSubsetSignature_matchgateIdentities
    {V E : Type*} [Fintype V] [Fintype E] {s : ℕ}
    {G : WeightedGraph V E ℂ} {ext : Fin s → V} (D : PlanarDrawing G ext) :
    MatchgateIdentities (deletionSubsetSignature G ext) :=
  MatchgateWidth.deletionSubsetSignature_matchgateIdentities G ext D.external_injective
    D.boundaryPathNoncrossing

/-- Exact geometric disk realizability implies all matchgate identities. The
geometric model is unchanged: the algebraic conclusion is proved from its
continuous edge drawings and weighted perfect-matching sum. -/
theorem DiskRealizable.matchgateIdentities {s : ℕ} {f : (Fin s → Bool) → ℂ}
    (hf : DiskRealizable f) : MatchgateIdentities (fun S => f (fun i => decide (i ∈ S))) := by
  obtain ⟨n, m, G, ext, ⟨D⟩, hf⟩ := hf
  simpa only [hf] using D.deletionSignature_matchgateIdentities

/-- The public exact disk-matchgate predicate therefore implies MGI, rather
than assuming it as part of membership. -/
theorem IsDiskMatchgateSignature.matchgateIdentities {s : ℕ}
    {f : (Fin s → Bool) → ℂ} (hf : IsDiskMatchgateSignature f) :
    MatchgateIdentities (fun S => f (fun i => decide (i ∈ S))) :=
  DiskRealizable.matchgateIdentities hf

end
end MatchgateWidth
