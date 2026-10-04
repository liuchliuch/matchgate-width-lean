import MatchgateWidth.StrongExteriorAccess
import MatchgateWidth.MatchingGluing
import MatchgateWidth.MatchingReindex

/-!
# Actual disk bridge assembly

Two independently drawn matching graphs in disjoint carriers can be joined by
specified simple bridge arcs whose interiors lie outside both carriers. The
construction below proves every edge/vertex nonintersection condition of the
assembled graph. It never assumes an MGI for the output signature.

This is an embedding operation, not a theorem that every ordered finite
network admits a compatible many-wire routing. The latter remains a separate
topological existence statement.
-/
namespace MatchgateWidth
noncomputable section

namespace PlaneDrawing
variable {V W E F : Type*} {G : WeightedGraph V E ℂ} {H : WeightedGraph W F ℂ}

/-- Two full carriers separate every point of the component drawings. -/
structure DisjointCarriers (P : PlaneDrawing G) (Q : PlaneDrawing H) where
  left : Set ℂ
  right : Set ℂ
  disjoint : Disjoint left right
  left_vertex : ∀ v, P.vertex v ∈ left
  right_vertex : ∀ w, Q.vertex w ∈ right
  left_edge : ∀ e t, P.edge e t ∈ left
  right_edge : ∀ f t, Q.edge f t ∈ right

/-- Disjoint union on actual graph identities and actual drawing points. -/
def disjointUnion (P : PlaneDrawing G) (Q : PlaneDrawing H)
    (C : DisjointCarriers P Q) : PlaneDrawing (disjointUnionGraph G H) where
  vertex := Sum.elim P.vertex Q.vertex
  vertex_injective := by
    rintro (v | w) (v' | w') h
    all_goals dsimp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (P.vertex_injective h)
    · exact (Set.disjoint_left.mp C.disjoint (C.left_vertex v)
        (h.symm ▸ C.right_vertex w')).elim
    · exact (Set.disjoint_left.mp C.disjoint (h.symm ▸ C.left_vertex v')
        (C.right_vertex w)).elim
    · exact congrArg Sum.inr (Q.vertex_injective h)
  edge := Sum.elim P.edge Q.edge
  edge_continuous := by rintro (e | f); exact P.edge_continuous e; exact Q.edge_continuous f
  edge_injective := by rintro (e | f); exact P.edge_injective e; exact Q.edge_injective f
  edge_left := by rintro (e | f); exact P.edge_left e; exact Q.edge_left f
  edge_right := by rintro (e | f); exact P.edge_right e; exact Q.edge_right f
  interior_avoids_vertices := by
    rintro (e | f) t ht0 ht1 (v | w) h
    all_goals dsimp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact P.interior_avoids_vertices e t ht0 ht1 v h
    · exact Set.disjoint_left.mp C.disjoint (C.left_edge e t) (h.symm ▸ C.right_vertex w)
    · exact Set.disjoint_left.mp C.disjoint (h.symm ▸ C.left_vertex v) (C.right_edge f t)
    · exact Q.interior_avoids_vertices f t ht0 ht1 w h
  interiors_disjoint := by
    rintro (e | f) (e' | f') hne t u ht0 ht1 hu0 hu1 h
    all_goals dsimp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact P.interiors_disjoint e e' (fun he => hne (congrArg Sum.inl he))
        t u ht0 ht1 hu0 hu1 h
    · exact Set.disjoint_left.mp C.disjoint (C.left_edge e t) (h.symm ▸ C.right_edge f' u)
    · exact Set.disjoint_left.mp C.disjoint (h.symm ▸ C.left_edge e' u) (C.right_edge f t)
    · exact Q.interiors_disjoint f f' (fun hf => hne (congrArg Sum.inr hf))
        t u ht0 ht1 hu0 hu1 h

/-- Data for genuinely drawing all bridge edges in the free space between the
component carriers. Endpoints and parameter directions are fixed by the graph. -/
structure BridgeRouting {B : Type*} (P : PlaneDrawing G) (Q : PlaneDrawing H)
    (C : DisjointCarriers P Q) (extL : B → V) (extR : B → W) where
  arc : ∀ b, Path (P.vertex (extL b)) (Q.vertex (extR b))
  simple : ∀ b, Function.Injective (arc b)
  outside_left : ∀ b t, 0 < t → t < 1 → arc b t ∉ C.left
  outside_right : ∀ b t, 0 < t → t < 1 → arc b t ∉ C.right
  disjoint_interiors : ∀ b d, b ≠ d → ∀ t u,
    0 < t → t < 1 → 0 < u → u < 1 → arc b t ≠ arc d u

/-- Glue actual matching graphs through their distinct unit-weight bridge
edges. All cross-component intersection obligations follow from the carriers
and routes; internal component geometry is reused unchanged. -/
def bridge {B : Type*} (P : PlaneDrawing G) (Q : PlaneDrawing H)
    (C : DisjointCarriers P Q) (extL : B → V) (extR : B → W)
    (R : BridgeRouting P Q C extL extR) :
    PlaneDrawing (bridgeGraph G H extL extR) where
  vertex := (P.disjointUnion Q C).vertex
  vertex_injective := (P.disjointUnion Q C).vertex_injective
  edge := Sum.elim (P.disjointUnion Q C).edge (fun b => R.arc b)
  edge_continuous := by
    rintro (e | b)
    · exact (P.disjointUnion Q C).edge_continuous e
    · exact (R.arc b).continuous
  edge_injective := by
    rintro (e | b)
    · exact (P.disjointUnion Q C).edge_injective e
    · exact R.simple b
  edge_left := by
    rintro (e | b)
    · exact (P.disjointUnion Q C).edge_left e
    · exact (R.arc b).source
  edge_right := by
    rintro (e | b)
    · exact (P.disjointUnion Q C).edge_right e
    · exact (R.arc b).target
  interior_avoids_vertices := by
    rintro (e | b) t ht0 ht1 v h
    · exact (P.disjointUnion Q C).interior_avoids_vertices e t ht0 ht1 v h
    · cases v with
      | inl v =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_left b t ht0 ht1 (h.symm ▸ C.left_vertex v)
      | inr w =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_right b t ht0 ht1 (h.symm ▸ C.right_vertex w)
  interiors_disjoint := by
    rintro (e | b) (f | d) hne t u ht0 ht1 hu0 hu1 h
    · exact (P.disjointUnion Q C).interiors_disjoint e f
        (fun he => hne (congrArg Sum.inl he)) t u ht0 ht1 hu0 hu1 h
    · cases e with
      | inl e =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_left d u hu0 hu1 (h ▸ C.left_edge e t)
      | inr f =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_right d u hu0 hu1 (h ▸ C.right_edge f t)
    · cases f with
      | inl e =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_left b t ht0 ht1 (h.symm ▸ C.left_edge e u)
      | inr f =>
        dsimp only [Sum.elim_inl, Sum.elim_inr, disjointUnion] at h
        exact R.outside_right b t ht0 ht1 (h.symm ▸ C.right_edge f u)
    · exact R.disjoint_interiors b d (fun he => hne (congrArg Sum.inr he))
        t u ht0 ht1 hu0 hu1 h

/-- The actual bridge assembly lies in the disk and has exactly the specified
external order when its explicit coordinates have these bounds and locations.
These are scalar/geometric conditions, not a signature-closure premise. -/
def bridgeDisk {B : Type*} {s : ℕ} (P : PlaneDrawing G) (Q : PlaneDrawing H)
    (C : DisjointCarriers P Q) (extL : B → V) (extR : B → W)
    (R : BridgeRouting P Q C extL extR)
    (hP : ∀ z ∈ C.left, ‖z‖ ≤ 1) (hQ : ∀ z ∈ C.right, ‖z‖ ≤ 1)
    (hR : ∀ b t, ‖R.arc b t‖ ≤ 1)
    (ext : Fin s → V ⊕ W) (hext : Function.Injective ext)
    (angle : Fin s → ℝ) (hangle0 : ∀ i, 0 < angle i)
    (hangle1 : ∀ i, angle i < 1) (hangle : StrictMono angle)
    (hlocation : ∀ i, (P.bridge Q C extL extR R).vertex (ext i) = boundaryPoint (angle i)) :
    PlanarDrawing (bridgeGraph G H extL extR) ext where
  vertex := (P.bridge Q C extL extR R).vertex
  vertex_injective := (P.bridge Q C extL extR R).vertex_injective
  edge := (P.bridge Q C extL extR R).edge
  edge_continuous := (P.bridge Q C extL extR R).edge_continuous
  edge_injective := (P.bridge Q C extL extR R).edge_injective
  edge_left := (P.bridge Q C extL extR R).edge_left
  edge_right := (P.bridge Q C extL extR R).edge_right
  interior_avoids_vertices := (P.bridge Q C extL extR R).interior_avoids_vertices
  interiors_disjoint := (P.bridge Q C extL extR R).interiors_disjoint
  vertex_in_disk := by
    rintro (v | w)
    · exact hP _ (C.left_vertex v)
    · exact hQ _ (C.right_vertex w)
  edge_in_disk := by
    rintro ((e | f) | b) t
    · exact hP _ (C.left_edge e t)
    · exact hQ _ (C.right_edge f t)
    · exact hR b t
  external_injective := hext
  angle := angle
  angle_pos := hangle0
  angle_lt_one := hangle1
  angle_strictMono := hangle
  external_vertex := hlocation

/-- The glued drawing yields an exact graph matchgate in its displayed
boundary order, after harmless finite enumeration of vertices and edges. -/
theorem bridgeDisk_exact {B : Type*} {s : ℕ}
    [Fintype V] [Fintype W] [Fintype E] [Fintype F] [Fintype B]
    (P : PlaneDrawing G) (Q : PlaneDrawing H)
    (C : DisjointCarriers P Q) (extL : B → V) (extR : B → W)
    (R : BridgeRouting P Q C extL extR)
    (hP : ∀ z ∈ C.left, ‖z‖ ≤ 1) (hQ : ∀ z ∈ C.right, ‖z‖ ≤ 1)
    (hR : ∀ b t, ‖R.arc b t‖ ≤ 1)
    (ext : Fin s → V ⊕ W) (hext : Function.Injective ext)
    (angle : Fin s → ℝ) (hangle0 : ∀ i, 0 < angle i)
    (hangle1 : ∀ i, angle i < 1) (hangle : StrictMono angle)
    (hlocation : ∀ i, (P.bridge Q C extL extR R).vertex (ext i) = boundaryPoint (angle i)) :
    ExactMatchgate (fun x => deletionSignature (bridgeGraph G H extL extR) ext
      (booleanWordEquiv s x)) := by
  apply (exactMatchgate_iff_booleanDiskRealizable _).mpr
  change DiskRealizable (fun x => deletionSignature (bridgeGraph G H extL extR) ext
    (booleanWordEquiv s ((booleanWordEquiv s).symm x)))
  simp only [Equiv.apply_symm_apply]
  exact diskRealizable_of_finite_drawing _ ext
    (P.bridgeDisk Q C extL extR R hP hQ hR ext hext angle hangle0 hangle1 hangle hlocation)

end PlaneDrawing
end
end MatchgateWidth
